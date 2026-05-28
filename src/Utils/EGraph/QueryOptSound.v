From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List Classes.RelationClasses.
Import ListNotations.
Open Scope list.

From Stdlib Require Import Logic.PropExtensionality
  Logic.FunctionalExtensionality.

From coqutil Require Import Map.Interface.

From Utils Require Import Utils UnionFind Monad ExtraMaps Relations Maps VC.
From Utils.EGraph Require Import Defs Semantics QueryOpt.
Import Monad.StateMonad.

(*
  This file states and proves that QueryOpt.optimize_sequent preserves
  the model-theoretic semantics of a sequent under the [good_sequent]
  precondition (which excludes the orphan-eqs edge case where the
  optimiser would be unsound).

  Status (multi-session work in progress):

  - Main theorem [optimize_sequent_equiv] is Qed-proved by composing
    [optimize_sequent_forward] and [optimize_sequent_reverse].
  - Both direction lemmas have full proofs of the empty-empty branch
    of [destruct seq_assumptions; destruct seq_conclusions], and
    `admit` for the three non-empty branches.
  - The remaining work is L11 [clauses_to_instance_sound], which
    builds the renaming<->assignment bridge between source variables
    (used by [model_satisfies_rule m s]) and canonical e-graph ids
    (used by [model_satisfies_rule m (optimize_sequent s)]).  Once
    L11 lands, the three non-empty branches reduce to standard
    state-monad reasoning over [rebuild_sound], [union_sound],
    [alloc_sound], [update_entry_sound], [force_equiv_sound].

  See /root/.claude/plans/queryopt-v-is-a-file-hidden-nest.md for the
  full strategy and L11's intended signature.
*)

Section WithMap.
  Context
    (idx : Type)
      (Eqb_idx : Eqb idx)
      (Eqb_idx_ok : Eqb_ok Eqb_idx)
      (lt : idx -> idx -> Prop)
      (idx_succ : idx -> idx)
      (idx_zero : WithDefault idx)
    (symbol : Type)
      (Eqb_symbol : Eqb symbol)
      (Eqb_symbol_ok : Eqb_ok Eqb_symbol)
      (default_symbol : WithDefault symbol).

  Existing Instance Eqb_idx.
  Existing Instance idx_zero.
  Existing Instance default_symbol.

  Context (symbol_map : forall A, map.map symbol A)
    (symbol_map_ok : forall A, @map.ok _ _ (symbol_map A))
    (symbol_map_plus : map_plus symbol_map).

  Context
      (idx_map : forall A, map.map idx A)
        (idx_map_plus : map_plus idx_map)
        (idx_map_ok : forall A, map.ok (idx_map A))
        (idx_trie : forall A, map.map (list idx) A)
        (idx_trie_ok : forall A, map.ok (idx_trie A))
        (idx_trie_plus : map_plus idx_trie).

  Notation atom := (atom idx symbol).
  Notation clause := (clause idx symbol).
  Notation sequent := (sequent idx symbol).
  Notation instance := (instance idx symbol symbol_map idx_map idx_trie unit).

  Section ForModel.
    Context (m : model symbol).

    Notation domain := (m.(domain symbol)).

    Notation atom_sound_for_model :=
      (atom_sound_for_model idx symbol idx_map m).
    Notation eq_sound_for_model :=
      (eq_sound_for_model idx symbol idx_map m).
    Notation clause_sound_for_model :=
      (clause_sound_for_model idx symbol idx_map m).

    (* L2: monotonicity of soundness under map extension. *)
    Lemma list_Mmap_get_extend (a1 a2 : idx_map domain) (xs : list idx) (vs : list domain) :
      map.extends a2 a1 ->
      list_Mmap (map.get a1) xs = Some vs ->
      list_Mmap (map.get a2) xs = Some vs.
    Proof.
      intros Hext; revert vs; induction xs; intros vs Hxs; cbn in *.
      - exact Hxs.
      - destruct (map.get a1 a) as [v|] eqn:Ha; cbn in Hxs; try discriminate.
        destruct (list_Mmap (map.get a1) xs) as [vs'|] eqn:Hvs; cbn in Hxs;
          try discriminate.
        inversion Hxs; subst vs.
        rewrite (Hext _ _ Ha).
        rewrite (IHxs _ eq_refl). reflexivity.
    Qed.

    Lemma atom_sound_extend (a1 a2 : idx_map domain) (at_ : atom) :
      map.extends a2 a1 ->
      atom_sound_for_model a1 at_ ->
      atom_sound_for_model a2 at_.
    Proof.
      intros Hext.
      unfold Semantics.atom_sound_for_model.
      destruct (list_Mmap (map.get a1) at_.(atom_args)) as [args|] eqn:Hargs;
        cbn [Is_Some_satisfying]; try tauto.
      destruct (map.get a1 at_.(atom_ret)) as [out|] eqn:Hret;
        cbn [Is_Some_satisfying]; try tauto.
      intros Hi.
      rewrite (list_Mmap_get_extend _ _ _ _ Hext Hargs). cbn [Is_Some_satisfying].
      rewrite (Hext _ _ Hret). cbn [Is_Some_satisfying].
      exact Hi.
    Qed.

    Lemma eq_sound_extend (a1 a2 : idx_map domain) (x y : idx) :
      map.extends a2 a1 ->
      eq_sound_for_model a1 x y ->
      eq_sound_for_model a2 x y.
    Proof.
      intros Hext.
      unfold Semantics.eq_sound_for_model.
      destruct (map.get a1 x) as [vx|] eqn:Hx; cbn [Is_Some_satisfying]; try tauto.
      destruct (map.get a1 y) as [vy|] eqn:Hy; cbn [Is_Some_satisfying]; try tauto.
      intros Heq.
      rewrite (Hext _ _ Hx). cbn [Is_Some_satisfying].
      rewrite (Hext _ _ Hy). cbn [Is_Some_satisfying].
      exact Heq.
    Qed.

    Lemma clause_sound_extend (a1 a2 : idx_map domain) (c : clause) :
      map.extends a2 a1 ->
      clause_sound_for_model a1 c ->
      clause_sound_for_model a2 c.
    Proof.
      intros Hext; destruct c; cbn.
      - eapply eq_sound_extend; eauto.
      - eapply atom_sound_extend; eauto.
    Qed.

    Lemma all_clause_sound_extend (a1 a2 : idx_map domain) (cs : list clause) :
      map.extends a2 a1 ->
      all (clause_sound_for_model a1) cs ->
      all (clause_sound_for_model a2) cs.
    Proof.
      intros Hext; induction cs as [| c cs IH]; cbn; intros H; trivial.
      destruct H as [Hc Hcs].
      split.
      - eapply clause_sound_extend; eauto.
      - apply IH; exact Hcs.
    Qed.

    (* Realising the second draft from Semantics.v:306-312.
       Precondition weakened from `set_eq (map.keys a) (forall_vars r)` to
       `forall x in forall_vars r, has_key x a` — the strict equality fails
       on the optimised side after canonicalisation renames keys. *)
    Definition model_satisfies_rule (r : sequent) : Prop :=
      forall a : idx_map domain,
        (forall x, In x (forall_vars r) -> Sep.has_key x a) ->
        all (clause_sound_for_model a) r.(seq_assumptions) ->
        exists a' : idx_map domain,
          map.extends a' a /\
          all (clause_sound_for_model a') r.(seq_conclusions).

  End ForModel.

  Definition sequent_equiv (s1 s2 : sequent) : Prop :=
    forall m, model_satisfies_rule m s1 <-> model_satisfies_rule m s2.

  #[export] Instance sequent_equiv_Reflexive : Reflexive sequent_equiv.
  Proof. intros s m; reflexivity. Qed.

  #[export] Instance sequent_equiv_Symmetric : Symmetric sequent_equiv.
  Proof. intros s1 s2 H m; symmetry; apply H. Qed.

  #[export] Instance sequent_equiv_Transitive : Transitive sequent_equiv.
  Proof. intros s1 s2 s3 H12 H23 m; etransitivity; [apply H12 | apply H23]. Qed.

  (* The full external type of [optimize_sequent] is
       optimize_sequent : forall idx, Eqb idx -> (idx -> idx) -> WithDefault idx ->
                          forall symbol, ... -> sequent -> nat -> sequent.
     We hide all the section-level arguments and the fuel choice in a
     local notation so the theorem reads cleanly. *)
  Notation optimize_sequent s :=
    (QueryOpt.optimize_sequent idx Eqb_idx idx_succ idx_zero
       symbol symbol_map idx_map idx_trie s
       (let var_count :=
          length (flat_map (clause_vars idx symbol) s.(seq_assumptions)
                  ++ flat_map (clause_vars idx symbol) s.(seq_conclusions))
        in var_count * var_count)).

  (* ============================================================== *)
  (* L1: db_to_atoms ↔ atom_in_db bridge                              *)
  (* ============================================================== *)

  Notation atom_in_db := (atom_in_db idx symbol symbol_map idx_trie unit).
  Notation db_to_atoms := (@db_to_atoms idx symbol symbol_map idx_trie unit).
  Notation table_atoms := (@table_atoms idx symbol idx_trie unit).
  Notation row_to_atom := (@row_to_atom idx symbol unit).

  Lemma db_to_atoms_empty :
    db_to_atoms (map.empty : symbol_map (idx_trie (db_entry idx unit))) = [].
  Proof.
    unfold Semantics.db_to_atoms.
    cbn.
    unfold map.tuples. rewrite Properties.map.fold_empty. reflexivity.
  Qed.

  (* force_uf on an empty union-find is a no-op.  Useful for reducing
     optimize_sequent on sequents with no clauses (whose assumption
     egraph stays empty after clauses_to_instance). *)
  Lemma force_uf_empty :
    force_uf idx Eqb_idx idx_map (UnionFind.empty _ _ _ idx_zero)
    = (tt, UnionFind.empty _ _ _ idx_zero).
  Proof.
    unfold force_uf, map.keys, map.tuples.
    unfold UnionFind.empty. cbn [parent].
    rewrite Properties.map.fold_empty.
    cbn. reflexivity.
  Qed.

  Lemma map_tuples_empty {K V} {mp : map.map K V} {mp_ok : map.ok mp}
    : map.tuples (@map.empty K V mp) = [].
  Proof.
    unfold map.tuples; rewrite Properties.map.fold_empty; reflexivity.
  Qed.

  (* ============================================================== *)
  (* L11: clauses_to_instance soundness                              *)
  (* ============================================================== *)

  (* The bridge function: extend a source-vars assignment to also
     interpret the e-graph ids by composing through the renaming. *)
  Definition extend_via_sub {A} (i : idx_map A) (sub : named_list idx idx)
    : idx_map A :=
    fold_right (fun '(x, y) acc =>
                  match map.get i x with
                  | Some d => map.put acc y d
                  | None => acc
                  end) i sub.

  (* L11 (preservation of egraph_ok across clauses_to_instance).  The
     full L11 also extends the interpretation and tracks the renaming;
     this signature is the structural skeleton — the inductive cases
     are filled by alloc_sound, union_sound, update_entry_sound. *)
  (* rename_lookup behaviour: hit returns input unchanged. *)
  Lemma rename_lookup_hit (x : idx) (sub0 : named_list idx idx)
        (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) (y : idx) :
    named_list_lookup_err sub0 x = Some y ->
    rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit
      x sub0 e0 = ((y, sub0), e0).
  Proof.
    intros Hl. unfold rename_lookup. rewrite Hl. reflexivity.
  Qed.

  (* rename_lookup behaviour: miss invokes alloc with extended sub. *)
  Lemma rename_lookup_miss (x : idx) (sub0 : named_list idx idx)
        (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    named_list_lookup_err sub0 x = None ->
    forall y e1,
      alloc idx idx_succ symbol symbol_map idx_map idx_trie unit e0 = (y, e1) ->
      rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit
        x sub0 e0 = ((y, (x,y)::sub0), e1).
  Proof.
    intros Hl y e1 Ha. unfold rename_lookup. rewrite Hl.
    cbn. rewrite Ha. reflexivity.
  Qed.

  (* ============================================================== *)
  (* Layer A primitives needed by L11 but not yet in Semantics.v.    *)
  (* These should eventually land alongside union_sound, alloc_sound *)
  (* in Semantics.v.                                                  *)
  (* ============================================================== *)

  (* Helper: find_aux preserves the set of keys in the parent map.
     [find_aux] either (a) returns the parent unchanged (fuel exhausted,
     missing key, or self-loop) or (b) [map.put]s an existing key with a
     new value.  Neither operation removes a key. *)
  Lemma find_aux_keys_preserved (mr : nat) :
    forall (i : idx) (pa : idx_map idx) z,
      Sep.has_key z pa ->
      Sep.has_key z (snd (find_aux idx Eqb_idx (idx_map idx) mr i pa)).
  Proof.
    induction mr; intros i pa z Hz.
    - cbn. exact Hz.
    - cbn. destruct (map.get pa i) as [a|] eqn:Hpai; [|exact Hz].
      eqb_case a i; [exact Hz|].
      destruct (find_aux idx Eqb_idx (idx_map idx) mr a pa) as [v p'] eqn:Hfa.
      cbn.
      pose proof (IHmr a pa z Hz) as IH.
      rewrite Hfa in IH. cbn in IH.
      unfold Sep.has_key in *.
      eqb_case z i.
      + rewrite map.get_put_same. exact I.
      + rewrite map.get_put_diff by congruence. exact IH.
  Qed.

  Lemma UnionFind_find_keys_preserved
        (uf : union_find idx (idx_map idx) (idx_map nat)) (x : idx) :
    forall z,
      Sep.has_key z uf.(parent) ->
      Sep.has_key z (fst (UnionFind.find uf x)).(parent).
  Proof.
    intros z Hz.
    destruct uf as [ra pa mr nx].
    cbn [parent] in Hz.
    unfold UnionFind.find.
    pose proof (find_aux_keys_preserved (S mr) x pa z Hz) as Hk.
    destruct (find_aux idx Eqb_idx (idx_map idx) (S mr) x pa) as [cx f] eqn:Hfa.
    cbn [snd] in Hk.
    cbn [fst parent]. exact Hk.
  Qed.

  Lemma Defs_find_keys_preserved (x : idx) :
    forall e z,
      Sep.has_key z (parent (equiv e)) ->
      Sep.has_key z
        (parent (equiv (snd
          (@Defs.find idx Eqb_idx symbol symbol_map idx_map idx_trie unit x e)))).
  Proof.
    intros e z Hz.
    unfold Defs.find.
    destruct (UnionFind.find (equiv e) x) as [uf' v'] eqn:Hf.
    cbn.
    pose proof (UnionFind_find_keys_preserved (equiv e) x z Hz) as Hk.
    rewrite Hf in Hk. cbn in Hk. exact Hk.
  Qed.

  Lemma UnionFind_union_keys_preserved
        (uf : union_find idx (idx_map idx) (idx_map nat)) (x y : idx) :
    forall z,
      Sep.has_key z uf.(parent) ->
      Sep.has_key z
        (fst (UnionFind.union idx Eqb_idx (idx_map idx) (idx_map nat) uf x y)).(parent).
  Proof.
    intros z Hz.
    unfold UnionFind.union.
    destruct (UnionFind.find uf x) as [uf' cx] eqn:Hf1.
    destruct (UnionFind.find uf' y) as [uf'' cy] eqn:Hf2.
    cbn.
    pose proof (UnionFind_find_keys_preserved uf x z Hz) as Hz1.
    rewrite Hf1 in Hz1. cbn in Hz1.
    pose proof (UnionFind_find_keys_preserved uf' y z Hz1) as Hz2.
    rewrite Hf2 in Hz2. cbn in Hz2.
    eqb_case cx cy.
    { exact Hz2. }
    destruct (Nat.compare _ _); cbn in *;
      unfold Sep.has_key in *.
    - eqb_case z cy.
      + rewrite map.get_put_same. exact I.
      + rewrite map.get_put_diff by congruence. exact Hz2.
    - eqb_case z cy.
      + rewrite map.get_put_same. exact I.
      + rewrite map.get_put_diff by congruence. exact Hz2.
    - eqb_case z cx.
      + rewrite map.get_put_same. exact I.
      + rewrite map.get_put_diff by congruence. exact Hz2.
  Qed.

  (* union extends the key-set of the union-find. *)
  Lemma union_extends_keys (x y : idx) :
    vc (@Defs.union idx Eqb_idx symbol symbol_map idx_map idx_trie unit _ x y)
       (fun e res =>
          forall z, Sep.has_key z e.(equiv).(parent) ->
                    Sep.has_key z (snd res).(equiv).(parent)).
  Proof.
    unfold vc.
    intros e z Hz.
    unfold Defs.union; cbn [Mbind StateMonad.state_monad Mret].
    destruct (@Defs.find idx Eqb_idx symbol symbol_map idx_map idx_trie unit x e)
      as [v0 e1] eqn:Hf1.
    cbn [fst snd].
    assert (Hz1 : Sep.has_key z (parent (equiv e1))).
    { pose proof (Defs_find_keys_preserved x e z Hz) as Hp.
      rewrite Hf1 in Hp. cbn in Hp. exact Hp. }
    destruct (@Defs.find idx Eqb_idx symbol symbol_map idx_map idx_trie unit y e1)
      as [v1 e2] eqn:Hf2.
    cbn [fst snd].
    assert (Hz2 : Sep.has_key z (parent (equiv e2))).
    { pose proof (Defs_find_keys_preserved y e1 z Hz1) as Hp.
      rewrite Hf2 in Hp. cbn in Hp. exact Hp. }
    eqb_case v0 v1.
    { cbn. exact Hz2. }
    pose proof (UnionFind_union_keys_preserved (equiv e2) v0 v1 z Hz2) as Hp.
    destruct (UnionFind.union idx Eqb_idx (idx_map idx) (idx_map nat) (equiv e2) v0 v1)
      as [uf' v'] eqn:Hu.
    cbn [fst] in Hp.
    destruct (eqb v0 v'); cbn [snd equiv parent]; exact Hp.
  Qed.

  (* union preserves the full egraph_ok record (not just union_find_ok). *)
  Lemma union_preserves_egraph_ok (x y : idx) :
    vc (@Defs.union idx Eqb_idx symbol symbol_map idx_map idx_trie unit _ x y)
       (fun e res =>
          Semantics.egraph_ok idx lt symbol symbol_map idx_map idx_trie unit e ->
          Sep.has_key x e.(equiv).(parent) ->
          Sep.has_key y e.(equiv).(parent) ->
          Semantics.egraph_ok idx lt symbol symbol_map idx_map idx_trie unit (snd res)).
  Proof.
    unfold vc; intros e Hok Hkx Hky.
    pose proof (egraph_equiv_ok _ _ _ _ _ _ _ _ Hok) as Hexists_roots.
    epose proof (@Semantics.union_sound idx _ Eqb_idx_ok lt idx_succ idx_zero
                  symbol symbol_map idx_map idx_map_ok idx_trie unit _ x y e
                  Hexists_roots Hkx Hky) as Hus.
    pose proof (union_extends_keys x y) as Hext.
    unfold vc in Hext. specialize (Hext e).
    destruct (Defs.union x y e) as [v_u e_u] eqn:Hu_eq.
    cbn [snd fst] in *.
    destruct Hus as (Hdb_u & [roots_u Hroots_u] & Hper_u & Hpar_u & Hwl_rel_u & _).
    (* Hper_lift: pre-union PER is included in post-union PER *)
    assert (Hper_lift : forall i1 i2,
              uf_rel_PER idx (idx_map idx) (idx_map nat) (equiv e) i1 i2 ->
              uf_rel_PER idx (idx_map idx) (idx_map nat) (equiv e_u) i1 i2).
    { intros i1 i2 Hi12. apply Hper_u.
      unfold union_closure_PER. apply PER_clo_base. left. exact Hi12. }
    constructor.
    1: { exists roots_u. exact Hroots_u. }
    1: { (* worklist_ok *)
         pose proof (worklist_ok _ _ _ _ _ _ _ _ Hok) as Hwlok_e.
         destruct Hwl_rel_u as [Hwl_same | Hwl_new].
         { rewrite Hwl_same. eapply all_wkn; [|exact Hwlok_e].
           intros ent _ Hp. destruct ent as [old new improved | x_a];
             cbn in *; [apply Hper_lift; exact Hp | exact I]. }
         { destruct Hwl_new as (v_old & v_new & improved & Hwl_eq & Hper_old & Hper_new).
           rewrite Hwl_eq. cbn. split.
           1: { (* uf_rel_PER e_u v_old v_new *)
                assert (Hr_xy : uf_rel_PER idx (idx_map idx) (idx_map nat) (equiv e_u) x y).
                { apply Hper_u. apply PER_clo_base. right. unfold singleton_rel.
                  split; reflexivity. }
                unfold uf_rel_PER in *.
                eapply PER_clo_trans; [exact Hper_old|].
                eapply PER_clo_trans; [exact Hr_xy|].
                apply PER_clo_sym. exact Hper_new. }
           eapply all_wkn; [|exact Hwlok_e].
           intros ent2 _ Hp2. destruct ent2 as [old2 new2 improved2 | x_a2];
             cbn in *; [apply Hper_lift; exact Hp2 | exact I]. } }
    1: { (* parents_ok *)
         rewrite <- Hpar_u.
         intros x_p s_p Hgs.
         pose proof (parents_ok _ _ _ _ _ _ _ _ Hok _ _ Hgs) as Hpok.
         eapply all_wkn; [|exact Hpok].
         intros b _ Hbup.
         destruct Hbup as (bb & Hca & Hbain).
         destruct Hca as (Hfn & Hargs & Hret).
         exists bb. split.
         1: { unfold atom_canonical_equiv. split; [exact Hfn|]. split.
              1: { clear -Hargs Hper_lift.
                   revert Hargs. generalize (atom_args b), (atom_args bb).
                   intros l1 l2. revert l2.
                   induction l1 as [|w ws IH]; destruct l2 as [|z zs];
                     cbn; auto; try tauto.
                   intros [Hw Hws]. split.
                   { apply Hper_lift. exact Hw. }
                   { apply IH. exact Hws. } }
              apply Hper_lift. exact Hret. }
         unfold atom_in_egraph. rewrite <- Hdb_u. exact Hbain. }
    (* db_idxs_in_equiv *)
    rewrite <- Hdb_u. intros b Hb.
    pose proof (db_idxs_in_equiv _ _ _ _ _ _ _ _ Hok _ Hb) as [Hka Hkr].
    split.
    1: { eapply all_wkn; [|exact Hka].
         intros j _ Hj. apply Hext. exact Hj. }
    apply Hext. exact Hkr.
  Qed.

  (* union preserves egraph_sound_for_interpretation when the two ids
     are eq_sound_for_model-related under the interpretation. *)
  Lemma union_preserves_egraph_sound_for_interpretation (m : model symbol) (Hm : model_ok symbol m)
        (x y : idx) (i : idx_map (m.(domain symbol))) :
    vc (@Defs.union idx Eqb_idx symbol symbol_map idx_map idx_trie unit _ x y)
       (fun e res =>
          Semantics.egraph_ok idx lt symbol symbol_map idx_map idx_trie unit e ->
          Semantics.egraph_sound_for_interpretation
            idx symbol symbol_map idx_map idx_trie unit m i e ->
          Sep.has_key x e.(equiv).(parent) ->
          Sep.has_key y e.(equiv).(parent) ->
          Semantics.eq_sound_for_model idx symbol idx_map m i x y ->
          Semantics.egraph_sound_for_interpretation
            idx symbol symbol_map idx_map idx_trie unit m i (snd res)).
  Proof.
    unfold vc; intros e Hok Hsnd Hkx Hky Heq_xy.
    pose proof (egraph_equiv_ok _ _ _ _ _ _ _ _ Hok) as Hexists_roots.
    epose proof (@Semantics.union_sound idx _ Eqb_idx_ok lt idx_succ idx_zero
                  symbol symbol_map idx_map idx_map_ok idx_trie unit _ x y e
                  Hexists_roots Hkx Hky) as Hus.
    pose proof (union_extends_keys x y) as Hext.
    unfold vc in Hext. specialize (Hext e).
    destruct (Defs.union x y e) as [v_u e_u] eqn:Hu_eq.
    cbn [snd fst] in *.
    destruct Hus as (Hdb_u & _ & Hper_u & _ & _ & _).
    constructor.
    1: { (* idx_interpretation_wf: unchanged interpretation *)
         pose proof (idx_interpretation_wf _ _ _ _ _ _ _ _ _ Hsnd) as Hi_wf.
         exact Hi_wf. }
    1: { (* interpretation_exact: keys extended via union_extends_keys *)
         intros y0 Hy0.
         pose proof (interpretation_exact _ _ _ _ _ _ _ _ _ Hsnd y0 Hy0) as Hkey.
         apply Hext. exact Hkey. }
    1: { (* atom_interpretation: db preserved *)
         intros a Ha.
         pose proof (atom_interpretation _ _ _ _ _ _ _ _ _ Hsnd a) as Ha_snd.
         apply Ha_snd. unfold atom_in_egraph. rewrite Hdb_u. exact Ha. }
    (* rel_interpretation: lift the closure *)
    intros i1 i2 Hi12.
    apply Hper_u in Hi12.
    induction Hi12 as [a b H1 | a b c IHab Hab IHbc Hbc | a b IHab Hab].
    - destruct H1 as [Hold | Hnew].
      + (* Old PER pair: use old rel_interpretation *)
        pose proof (rel_interpretation _ _ _ _ _ _ _ _ _ Hsnd a b) as Hi_rel.
        apply Hi_rel; exact Hold.
      + (* New pair: (a, b) = (x, y) by singleton_rel *)
        destruct Hnew as [Hax Hby]; subst.
        exact Heq_xy.
    - (* Trans *)
      eapply (eq_sound_for_model_trans idx symbol idx_map m); eauto.
    - (* Sym *)
      eapply (eq_sound_for_model_Symmetric idx symbol idx_map m); eauto.
  Qed.

  (* ============================================================== *)
  (* Phase 3 auxiliaries: state-read predicates exposed by           *)
  (* egraph_reducing_equal_step's termination check.                  *)
  (* ============================================================== *)

  (* [are_unified x y = true] in a state where the model interprets
     both ids means they are eq_sound_for_model under that
     interpretation.  Proof: find x and find y both return the same
     canonical representative; both are PER-related to their finds; so
     x and y are PER-related; apply [rel_interpretation]. *)
  Lemma are_unified_sound (m : model symbol) (i : idx_map m.(domain symbol))
        (x y : idx) :
    vc (@are_unified idx Eqb_idx symbol symbol_map idx_map idx_trie unit x y)
       (fun e res =>
          Semantics.egraph_ok idx lt symbol symbol_map idx_map idx_trie unit e ->
          Semantics.egraph_sound_for_interpretation
            idx symbol symbol_map idx_map idx_trie unit m i e ->
          Sep.has_key x e.(equiv).(parent) ->
          Sep.has_key y e.(equiv).(parent) ->
          fst res = true ->
          Semantics.eq_sound_for_model idx symbol idx_map m i x y).
  Proof.
    unfold vc; intros e Hok Hsnd Hkx Hky Hres.
    unfold are_unified in *; cbn [Mbind StateMonad.state_monad Mret] in *.
    pose proof (egraph_equiv_ok _ _ _ _ _ _ _ _ Hok) as [roots Hroots].
    pose proof (Semantics.find_sound' idx Eqb_idx Eqb_idx_ok lt idx_zero
                  symbol symbol_map idx_map idx_map_ok idx_trie unit x roots) as Hfx_snd.
    unfold vc in Hfx_snd. specialize (Hfx_snd e).
    destruct (Defs.find x e) as [x1' s1] eqn:Hf1.
    cbn [fst snd] in Hfx_snd.
    specialize (Hfx_snd Hroots Hkx).
    destruct Hfx_snd as
      (Hdb_x & Hok_s1 & Hiff_x & Hpa_x & Hwl_x & Hki_x & Hin_x & Hxx').
    (* Now do find y on s1 *)
    pose proof (Semantics.find_sound' idx Eqb_idx Eqb_idx_ok lt idx_zero
                  symbol symbol_map idx_map idx_map_ok idx_trie unit y roots) as Hfy_snd.
    unfold vc in Hfy_snd. specialize (Hfy_snd s1).
    destruct (Defs.find y s1) as [x2' s2] eqn:Hf2.
    cbn [fst snd] in Hfy_snd.
    assert (Hky_s1 : Sep.has_key y (parent (equiv s1)))
      by (apply (proj1 (Hki_x y)); exact Hky).
    specialize (Hfy_snd Hok_s1 Hky_s1).
    destruct Hfy_snd as
      (Hdb_y & Hok_s2 & Hiff_y & Hpa_y & Hwl_y & Hki_y & Hin_y & Hyx').
    cbn [fst snd Mret StateMonad.state_monad] in Hres.
    (* eqb x1' x2' = true → x1' = x2' *)
    eqb_case x1' x2'; [|congruence].
    (* uf_rel_PER (equiv s2) x y via the two find results + trans/sym *)
    assert (Hxx'_s2 : uf_rel_PER idx (idx_map idx) (idx_map nat) (equiv s2) x x2')
      by (apply Hiff_y; exact Hxx').
    assert (Hxy_s2 : uf_rel_PER idx (idx_map idx) (idx_map nat) (equiv s2) x y).
    { unfold uf_rel_PER in *.
      eapply PER_clo_trans; [exact Hxx'_s2|].
      apply PER_clo_sym; exact Hyx'. }
    assert (Hxy_e : uf_rel_PER idx (idx_map idx) (idx_map nat) (equiv e) x y).
    { apply Hiff_x. apply Hiff_y. exact Hxy_s2. }
    pose proof (rel_interpretation _ _ _ _ _ _ _ _ _ Hsnd x y) as Hi_rel.
    apply Hi_rel; exact Hxy_e.
  Qed.

  (* A single [rename_lookup x] on a source var [x] whose source value is
     [dx]: extends the interpretation, preserves the renaming invariants,
     and yields a renamed id [x'] that interprets to [dx] and is a key.
     Either [x] was already renamed (hit; nothing changes) or it is freshly
     allocated (miss; one [alloc_sound] step). *)
  Lemma rename_lookup_sound
    (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x))
    (Hltt : Transitive lt) (m : model symbol) (Hm : model_ok symbol m)
    (a_src : idx_map (m.(domain symbol)))
    (x : idx) (dx : m.(domain symbol))
    (sub : named_list idx idx)
    (e : Defs.instance idx symbol symbol_map idx_map idx_trie unit)
    (i : idx_map (m.(domain symbol))) :
    Semantics.egraph_ok idx lt symbol symbol_map idx_map idx_trie unit e ->
    Semantics.egraph_sound_for_interpretation
      idx symbol symbol_map idx_map idx_trie unit m i e ->
    (forall x0 y0, In (x0, y0) sub ->
                   forall d, map.get a_src x0 = Some d -> map.get i y0 = Some d) ->
    (forall x0 y0, In (x0, y0) sub -> Sep.has_key y0 (parent (equiv e))) ->
    map.get a_src x = Some dx ->
    m.(domain_wf symbol) dx ->
    match rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
            unit x sub e with
    | (x', sub', e') =>
        exists i',
          map.extends i' i /\
          Semantics.egraph_ok idx lt symbol symbol_map idx_map idx_trie unit e' /\
          Semantics.egraph_sound_for_interpretation
            idx symbol symbol_map idx_map idx_trie unit m i' e' /\
          (forall x0 y0, In (x0, y0) sub' ->
                         forall d, map.get a_src x0 = Some d -> map.get i' y0 = Some d) /\
          (forall x0 y0, In (x0, y0) sub' -> Sep.has_key y0 (parent (equiv e'))) /\
          map.get i' x' = Some dx /\
          Sep.has_key x' (parent (equiv e')) /\
          (forall z, Sep.has_key z (parent (equiv e)) ->
                     Sep.has_key z (parent (equiv e')))
    end.
  Proof.
    intros Hok Hsnd Hren Hsubdom Hax Hwf_dx.
    unfold rename_lookup.
    destruct (named_list_lookup_err sub x) as [x'|] eqn:Hlook.
    { cbn.
      assert (Hin : In (x, x') sub) by (apply named_list_lookup_err_in; auto).
      exists i.
      split; [intros ? ? Hk; exact Hk|].
      split; [exact Hok|].
      split; [exact Hsnd|].
      split; [exact Hren|].
      split; [exact Hsubdom|].
      split; [exact (Hren _ _ Hin _ Hax)|].
      split; [exact (Hsubdom _ _ Hin)|].
      intros z Hz; exact Hz. }
    cbn -[alloc].
    destruct (alloc idx idx_succ symbol symbol_map idx_map idx_trie unit e)
      as [x_new e_alloc] eqn:Halloc.
    pose proof (Semantics.alloc_sound idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero
                  symbol symbol_map idx_map idx_map_ok idx_trie unit m
                  Hlti Hlts Hltt i dx Hwf_dx Hwf_dx) as Halloc_sound.
    unfold vc in Halloc_sound.
    specialize (Halloc_sound e).
    rewrite Halloc in Halloc_sound. cbn in Halloc_sound.
    specialize (Halloc_sound Hok Hsnd).
    destruct Halloc_sound as
      (Hok_a & Hsnd_a & Hi_xnew_none & Hk_xnew_e0_none & Hk_xnew_a &
       Hk_pres & Hdb_a & Hpar_a & Hwl_a).
    exists (map.put i x_new dx).
    split.
    { intros k d Hk. rewrite map.get_put_diff; [exact Hk|].
      intros Heq; subst k. rewrite Hi_xnew_none in Hk; discriminate. }
    split; [exact Hok_a|].
    split; [exact Hsnd_a|].
    split.
    { intros a b Hin d Hg.
      destruct Hin as [Heq|Hin].
      - inversion Heq; subst a b. rewrite map.get_put_same.
        rewrite Hax in Hg. inversion Hg; subst d. reflexivity.
      - rewrite map.get_put_diff.
        + exact (Hren _ _ Hin _ Hg).
        + intros Heq; subst b. pose proof (Hsubdom _ _ Hin) as Hkb.
          apply Hk_xnew_e0_none. exact Hkb. }
    split.
    { intros a b Hin.
      destruct Hin as [Heq|Hin].
      - inversion Heq; subst a b. exact Hk_xnew_a.
      - apply Hk_pres. exact (Hsubdom _ _ Hin). }
    split.
    { rewrite map.get_put_same. reflexivity. }
    split; [exact Hk_xnew_a|].
    exact Hk_pres.
  Qed.

  (* The list version of [rename_lookup_sound], by induction over the
     argument list: renaming a whole list of source vars (all sound,
     interpreting to [arg_doms]) yields renamed ids interpreting to the
     same [arg_doms], all keys, with the invariants preserved. *)
  Lemma list_Mmap_rename_lookup_sound
    (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x))
    (Hltt : Transitive lt) (m : model symbol) (Hm : model_ok symbol m)
    (a_src : idx_map (m.(domain symbol)))
    (args : list idx) (arg_doms : list (m.(domain symbol)))
    (sub : named_list idx idx)
    (e : Defs.instance idx symbol symbol_map idx_map idx_trie unit)
    (i : idx_map (m.(domain symbol))) :
    Semantics.egraph_ok idx lt symbol symbol_map idx_map idx_trie unit e ->
    Semantics.egraph_sound_for_interpretation
      idx symbol symbol_map idx_map idx_trie unit m i e ->
    (forall x0 y0, In (x0, y0) sub ->
                   forall d, map.get a_src x0 = Some d -> map.get i y0 = Some d) ->
    (forall x0 y0, In (x0, y0) sub -> Sep.has_key y0 (parent (equiv e))) ->
    list_Mmap (map.get a_src) args = Some arg_doms ->
    all (m.(domain_wf symbol)) arg_doms ->
    match list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                       idx_trie unit) args sub e with
    | (args', sub', e') =>
        exists i',
          map.extends i' i /\
          Semantics.egraph_ok idx lt symbol symbol_map idx_map idx_trie unit e' /\
          Semantics.egraph_sound_for_interpretation
            idx symbol symbol_map idx_map idx_trie unit m i' e' /\
          (forall x0 y0, In (x0, y0) sub' ->
                         forall d, map.get a_src x0 = Some d -> map.get i' y0 = Some d) /\
          (forall x0 y0, In (x0, y0) sub' -> Sep.has_key y0 (parent (equiv e'))) /\
          list_Mmap (map.get i') args' = Some arg_doms /\
          all (fun x' => Sep.has_key x' (parent (equiv e'))) args' /\
          (forall z, Sep.has_key z (parent (equiv e)) ->
                     Sep.has_key z (parent (equiv e')))
    end.
  Proof.
    revert arg_doms sub e i.
    induction args as [|a args0 IH];
      intros arg_doms sub e i Hok Hsnd Hren Hsubdom Hmap Hwf.
    - cbn in Hmap |- *.
      inversion Hmap; subst arg_doms.
      exists i.
      split; [intros ? ? Hk; exact Hk|].
      split; [exact Hok|].
      split; [exact Hsnd|].
      split; [exact Hren|].
      split; [exact Hsubdom|].
      split; [reflexivity|].
      split; [exact I|].
      intros z Hz; exact Hz.
    - cbn [list_Mmap] in Hmap.
      destruct (map.get a_src a) as [d_a|] eqn:Hda; [|discriminate].
      destruct (list_Mmap (map.get a_src) args0) as [ds|] eqn:Hds; [|discriminate].
      inversion Hmap; subst arg_doms.
      cbn [all] in Hwf.
      destruct Hwf as [Hwf_da Hwf_ds].
      pose proof (rename_lookup_sound Hlti Hlts Hltt m Hm a_src a d_a sub e i
                    Hok Hsnd Hren Hsubdom Hda Hwf_da) as Hrl.
      cbn [list_Mmap].
      destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                  idx_trie unit a sub e) as [ [a' sub1] e1 ] eqn:Hrla.
      destruct Hrl as (i1 & Hext1 & Hok1 & Hsnd1 & Hren1 & Hsubdom1 & Hi1a' &
                       Hka'1 & Hmono1).
      cbn -[rename_lookup list_Mmap] in *.
      rewrite Hrla.
      cbn [uncurry Basics.compose].
      pose proof (IH ds sub1 e1 i1 Hok1 Hsnd1 Hren1 Hsubdom1 eq_refl Hwf_ds) as HIH.
      unfold Basics.compose.
      destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map
                  idx_map idx_trie unit) args0 sub1 e1)
        as [ [args0' sub2] e2 ] eqn:Hlm.
      cbn [uncurry] in HIH |- *.
      destruct HIH as (i2 & Hext2 & Hok2 & Hsnd2 & Hren2 & Hsubdom2 & Hmap2 &
                       Hall2 & Hmono2).
      exists i2.
      split.
      { intros k v Hk. apply Hext2. apply Hext1. exact Hk. }
      split; [exact Hok2|].
      split; [exact Hsnd2|].
      split; [exact Hren2|].
      split; [exact Hsubdom2|].
      split.
      { assert (Hi2a' : map.get i2 a' = Some d_a) by (apply Hext2; exact Hi1a').
        cbn [list_Mmap]. rewrite Hi2a'. rewrite Hmap2. reflexivity. }
      split.
      { cbn [all]. split; [apply Hmono2; exact Hka'1 | exact Hall2]. }
      intros z Hz. apply Hmono2. apply Hmono1. exact Hz.
  Qed.

  (* Full L11 hypotheses, matching the existing soundness lemmas in
     Semantics.v (alloc_sound, update_entry_sound, union_sound):

     - Asymmetric/transitive/successor-respecting lt, model_ok m;
     - Initial egraph_ok + egraph_sound_for_interpretation;
     - A source assignment [a_src] under which the clauses are sound;
     - The renaming [sub0] is consistent: where [sub0] maps source
       var [x] to e-graph id [y], [i y] (the e-graph interpretation
       at [y]) equals [a_src x] (the source value).

     Conclusion: extend [i] to an [i'] so the post-clauses_to_instance
     e-graph is still sound, with the renaming [sub1] extending [sub0]
     and the consistency continuing to hold. *)
  Lemma clauses_to_instance_preserves_ok
    (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x))
    (Hltt : Transitive lt) (m : model symbol) (Hm : model_ok symbol m)
    (cs : list (Semantics.clause idx symbol))
    (sub0 : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit)
    (i : idx_map (m.(domain symbol)))
    (a_src : idx_map (m.(domain symbol))) :
    Semantics.egraph_ok idx lt symbol symbol_map idx_map idx_trie unit e0 ->
    Semantics.egraph_sound_for_interpretation
      idx symbol symbol_map idx_map idx_trie unit m i e0 ->
    (* Renaming consistency at the start. *)
    (forall x y, In (x, y) sub0 ->
                 forall d, map.get a_src x = Some d -> map.get i y = Some d) ->
    (* The renaming's codomain lives in the egraph's union-find. *)
    (forall x y, In (x, y) sub0 ->
                 Sep.has_key y (parent (equiv e0))) ->
    (* The source clauses are sound under a_src. *)
    all (Semantics.clause_sound_for_model idx symbol idx_map m a_src) cs ->
    match clauses_to_instance idx_succ (analysis_result:=unit) cs sub0 e0 with
    | (_, e1) =>
        Semantics.egraph_ok idx lt symbol symbol_map idx_map idx_trie unit e1 /\
        exists i',
          map.extends i' i /\
          Semantics.egraph_sound_for_interpretation
            idx symbol symbol_map idx_map idx_trie unit m i' e1
    end.
  Proof.
    revert sub0 e0 i.
    induction cs as [|c cs IH]; intros sub0 e0 i Hok Hsnd Hren Hsubdom Hcs.
    - cbn. split; [exact Hok|]. exists i.
      split; [intros ? ? Hk; exact Hk | exact Hsnd].
    - cbn. unfold add_clause_to_instance.
      destruct c as [x y | a].
      + (* eq_clause: split on whether each var is already in sub0. *)
        cbn. unfold Mret, lift, Mseq.
        destruct (named_list_lookup_err sub0 x) as [x'|] eqn:Hx;
        destruct (named_list_lookup_err sub0 y) as [y'|] eqn:Hy.
        * (* (hit, hit) sub-case — uses union_preserves_* admits *)
          cbn in Hcs. destruct Hcs as [Hc Hcs'].
          assert (Hinx : In (x, x') sub0) by (apply named_list_lookup_err_in; auto).
          assert (Hiny : In (y, y') sub0) by (apply named_list_lookup_err_in; auto).
          pose proof (Hsubdom _ _ Hinx) as Hkx.
          pose proof (Hsubdom _ _ Hiny) as Hky.
          cbn.
          destruct (@Defs.union idx Eqb_idx symbol symbol_map idx_map idx_trie unit _ x' y' e0)
            as [v e_unioned] eqn:Hu.
          rewrite (rename_lookup_hit _ _ _ _ Hx). cbn -[Defs.union].
          unfold Basics.compose, rename_lookup. rewrite Hy. cbn -[Defs.union].
          unfold Defs.union in Hu. cbn in Hu. rewrite Hu. cbn.
          apply IH; auto.
          { (* egraph_ok e_unioned *)
            pose proof (union_preserves_egraph_ok x' y' e0) as Hpres.
            unfold vc in Hpres.
            replace (union x' y' e0) with (v, e_unioned) in Hpres
              by (rewrite <- Hu; reflexivity).
            cbn in Hpres. apply Hpres; auto. }
          { (* egraph_sound m i e_unioned *)
            pose proof (union_preserves_egraph_sound_for_interpretation
                          m Hm x' y' i e0) as Hpres.
            unfold vc in Hpres.
            replace (union x' y' e0) with (v, e_unioned) in Hpres
              by (rewrite <- Hu; reflexivity).
            cbn in Hpres. apply Hpres; auto.
            unfold Semantics.eq_sound_for_model in Hc |- *.
            destruct (map.get a_src x) as [dx|] eqn:Hax; cbn in Hc; try tauto.
            destruct (map.get a_src y) as [dy|] eqn:Hay; cbn in Hc; try tauto.
            rewrite (Hren _ _ Hinx _ Hax).
            rewrite (Hren _ _ Hiny _ Hay).
            cbn. exact Hc. }
          { (* subdom for e_unioned *)
            intros x0 y0 Hin.
            pose proof (union_extends_keys x' y' e0) as Hpres.
            unfold vc in Hpres.
            replace (union x' y' e0) with (v, e_unioned) in Hpres
              by (rewrite <- Hu; reflexivity).
            cbn in Hpres. apply Hpres. exact (Hsubdom _ _ Hin). }
        * (* (hit, miss) — symmetric to (miss, hit): alloc for y *)
          cbn in Hcs. destruct Hcs as [Hc Hcs'].
          unfold Semantics.eq_sound_for_model in Hc.
          destruct (map.get a_src x) as [dx|] eqn:Hax; cbn in Hc; try tauto.
          destruct (map.get a_src y) as [dy|] eqn:Hay; cbn in Hc; try tauto.
          assert (Hinx : In (x, x') sub0) by (apply named_list_lookup_err_in; auto).
          pose proof (Hsubdom _ _ Hinx) as Hkx_e0.
          assert (Hwf_dy : m.(domain_wf symbol) dy).
          { destruct Hm as [HPER _ _ _ _].
            unfold domain_wf. eapply PER_Transitive;
              [apply PER_Symmetric; eassumption | eassumption]. }
          pose proof (Semantics.alloc_sound idx Eqb_idx Eqb_idx_ok lt idx_succ
                        idx_zero symbol symbol_map idx_map idx_map_ok idx_trie unit m
                        Hlti Hlts Hltt i dy Hwf_dy Hwf_dy) as Halloc_sound.
          unfold vc in Halloc_sound.
          destruct (alloc idx idx_succ symbol symbol_map idx_map idx_trie unit e0)
            as [y_new e_alloc] eqn:Halloc.
          specialize (Halloc_sound e0).
          rewrite Halloc in Halloc_sound. cbn in Halloc_sound.
          destruct Halloc_sound as
            (Hok_a & Hsnd_a & Hi_ynew_none & Hk_ynew_e0_none & Hk_ynew_a &
             Hk_pres & Hdb_a & Hpar_a & Hwl_a); auto.
          assert (Hxy_neq : x <> y).
          { intros Heq; subst y. rewrite Hx in Hy; discriminate. }
          (* rename_lookup x is HIT — returns (x', sub0, e0) unchanged *)
          rewrite (rename_lookup_hit _ _ _ _ Hx). cbn -[Defs.union].
          (* rename_lookup y is MISS — allocates y_new *)
          unfold Basics.compose, rename_lookup at 1.
          rewrite Hy. cbn -[Defs.union find].
          rewrite Halloc. cbn -[Defs.union find].
          (* Union x' y_new on e_alloc *)
          destruct (@Defs.union idx Eqb_idx symbol symbol_map idx_map idx_trie unit _
                       x' y_new e_alloc)
            as [v e_unioned] eqn:Hu.
          unfold Defs.union in Hu. cbn in Hu. rewrite Hu. cbn.
          assert (Hkx_a : Sep.has_key x' (parent (equiv e_alloc)))
            by (apply Hk_pres; exact Hkx_e0).
          assert (Hpost_IH : let (_, e1) := clauses_to_instance idx_succ cs
                                              ((y, y_new) :: sub0) e_unioned in
                             egraph_ok idx lt symbol symbol_map idx_map idx_trie
                               unit e1 /\
                             (exists i' : idx_map (domain symbol m),
                                map.extends i' (map.put i y_new dy) /\
                                egraph_sound_for_interpretation idx symbol
                                  symbol_map idx_map idx_trie unit m i' e1)).
          { apply IH.
            { pose proof (union_preserves_egraph_ok x' y_new e_alloc) as Hpres.
              unfold vc in Hpres.
              replace (union x' y_new e_alloc) with (v, e_unioned) in Hpres
                by (rewrite <- Hu; reflexivity).
              cbn in Hpres. apply Hpres; auto. }
            { pose proof (union_preserves_egraph_sound_for_interpretation
                            m Hm x' y_new (map.put i y_new dy) e_alloc) as Hpres.
              unfold vc in Hpres.
              replace (union x' y_new e_alloc) with (v, e_unioned) in Hpres
                by (rewrite <- Hu; reflexivity).
              cbn in Hpres. apply Hpres; auto.
              unfold Semantics.eq_sound_for_model.
              assert (Hx'_ne : x' <> y_new).
              { intros Heq. apply Hk_ynew_e0_none.
                rewrite <- Heq. exact Hkx_e0. }
              rewrite (map.get_put_diff _ _ _ _ Hx'_ne).
              rewrite (Hren _ _ Hinx _ Hax). cbn.
              rewrite map.get_put_same. cbn. exact Hc. }
            { intros a b Hin d Hg.
              destruct Hin as [Heq|Hin].
              - inversion Heq; subst a b.
                rewrite map.get_put_same.
                rewrite Hay in Hg. inversion Hg; subst d. reflexivity.
              - rewrite map.get_put_diff.
                + exact (Hren _ _ Hin _ Hg).
                + intros Heq. subst b.
                  pose proof (Hsubdom _ _ Hin) as Hkb.
                  apply Hk_ynew_e0_none. exact Hkb. }
            { intros a b Hin.
              pose proof (union_extends_keys x' y_new e_alloc) as Hpres.
              unfold vc in Hpres.
              replace (union x' y_new e_alloc) with (v, e_unioned) in Hpres
                by (rewrite <- Hu; reflexivity).
              cbn in Hpres.
              destruct Hin as [Heq|Hin].
              - inversion Heq; subst a b. apply Hpres. exact Hk_ynew_a.
              - apply Hpres. apply Hk_pres. apply (Hsubdom _ _ Hin). }
            { exact Hcs'. } }
          destruct (clauses_to_instance idx_succ cs ((y, y_new) :: sub0) e_unioned)
            as [pp e_final] eqn:Hci.
          destruct Hpost_IH as (Hok_f & i_final & Hext_f & Hsnd_f).
          split; [exact Hok_f|].
          exists i_final.
          split; [|exact Hsnd_f].
          intros k d Hk.
          apply Hext_f.
          rewrite map.get_put_diff; [exact Hk|].
          intros Heq. subst k. rewrite Hi_ynew_none in Hk. discriminate.
        * (* (miss, hit) *)
          cbn in Hcs. destruct Hcs as [Hc Hcs'].
          unfold Semantics.eq_sound_for_model in Hc.
          destruct (map.get a_src x) as [dx|] eqn:Hax; cbn in Hc; try tauto.
          destruct (map.get a_src y) as [dy|] eqn:Hay; cbn in Hc; try tauto.
          assert (Hiny : In (y, y') sub0) by (apply named_list_lookup_err_in; auto).
          pose proof (Hsubdom _ _ Hiny) as Hky_e0.
          assert (Hwf_dx : m.(domain_wf symbol) dx).
          { destruct Hm as [HPER _ _ _ _].
            unfold domain_wf. eapply PER_Transitive;
              [eassumption | apply PER_Symmetric; auto]. }
          (* Apply alloc_sound to allocate fresh id for x with witness dx. *)
          pose proof (Semantics.alloc_sound idx Eqb_idx Eqb_idx_ok lt idx_succ
                        idx_zero symbol symbol_map idx_map idx_map_ok idx_trie unit m
                        Hlti Hlts Hltt i dx Hwf_dx Hwf_dx) as Halloc_sound.
          unfold vc in Halloc_sound.
          destruct (alloc idx idx_succ symbol symbol_map idx_map idx_trie unit e0)
            as [x_new e_alloc] eqn:Halloc.
          specialize (Halloc_sound e0).
          rewrite Halloc in Halloc_sound. cbn in Halloc_sound.
          destruct Halloc_sound as
            (Hok_a & Hsnd_a & Hi_xnew_none & Hk_xnew_e0_none & Hk_xnew_a &
             Hk_pres & Hdb_a & Hpar_a & Hwl_a); auto.
          assert (Hxy_neq : x <> y).
          { intros Heq; subst y. rewrite Hx in Hy; discriminate. }
          assert (Hrm_x : rename_lookup idx Eqb_idx idx_succ symbol symbol_map
                            idx_map idx_trie unit x sub0 e0
                          = ((x_new, (x, x_new)::sub0), e_alloc)).
          { unfold rename_lookup. rewrite Hx. cbn. rewrite Halloc. reflexivity. }
          cbn.
          rewrite Hrm_x. cbn -[Defs.union].
          unfold Basics.compose, rename_lookup at 1.
          assert (Hy' : named_list_lookup_err ((x, x_new)::sub0) y = Some y').
          { cbn. case_match.
            - exfalso; apply Hxy_neq.
              pose proof (Eqb_idx_ok y x) as Hyx_dec.
              rewrite case_match_eqn in Hyx_dec.
              symmetry; exact Hyx_dec.
            - exact Hy. }
          rewrite Hy'. cbn -[Defs.union find].
          (* Apply the union step pattern from (hit, hit), now on e_alloc with
             extended interpretation (map.put i x_new dx). *)
          destruct (@Defs.union idx Eqb_idx symbol symbol_map idx_map idx_trie unit _
                       x_new y' e_alloc)
            as [v e_unioned] eqn:Hu.
          unfold Defs.union in Hu. cbn in Hu. rewrite Hu. cbn.
          (* Establish has_key y' in e_alloc via Hk_pres. *)
          assert (Hky_a : Sep.has_key y' (parent (equiv e_alloc)))
            by (apply Hk_pres; exact Hky_e0).
          (* Use IH with the extended interpretation (map.put i x_new dx).
             The result will also have its existential a' relative to that
             extended interp; we then convert back to extending i via map.put. *)
          assert (Hpost_IH : let (_, e1) := clauses_to_instance idx_succ cs
                                              ((x, x_new) :: sub0) e_unioned in
                             egraph_ok idx lt symbol symbol_map idx_map idx_trie
                               unit e1 /\
                             (exists i' : idx_map (domain symbol m),
                                map.extends i' (map.put i x_new dx) /\
                                egraph_sound_for_interpretation idx symbol
                                  symbol_map idx_map idx_trie unit m i' e1)).
          { apply IH.
          { pose proof (union_preserves_egraph_ok x_new y' e_alloc) as Hpres.
            unfold vc in Hpres.
            replace (union x_new y' e_alloc) with (v, e_unioned) in Hpres
              by (rewrite <- Hu; reflexivity).
            cbn in Hpres. apply Hpres; auto. }
          { pose proof (union_preserves_egraph_sound_for_interpretation
                          m Hm x_new y' (map.put i x_new dx) e_alloc) as Hpres.
            unfold vc in Hpres.
            replace (union x_new y' e_alloc) with (v, e_unioned) in Hpres
              by (rewrite <- Hu; reflexivity).
            cbn in Hpres. apply Hpres; auto.
            (* eq_sound m (map.put i x_new dx) x_new y' *)
            unfold Semantics.eq_sound_for_model.
            rewrite map.get_put_same.
            rewrite map.get_put_diff.
            - rewrite (Hren _ _ Hiny _ Hay). cbn. exact Hc.
            - (* x_new <> y' *)
              intros Heq. subst y'.
              apply Hk_xnew_e0_none. exact Hky_e0. }
          { (* renaming consistency for (x, x_new)::sub0 *)
            intros a b Hin d Hg.
            destruct Hin as [Heq|Hin].
            - inversion Heq; subst a b.
              rewrite map.get_put_same.
              rewrite Hax in Hg. inversion Hg; subst d. reflexivity.
            - rewrite map.get_put_diff.
              + pose proof (union_extends_keys x_new y' e_alloc) as Hpres.
                unfold vc in Hpres.
                replace (union x_new y' e_alloc) with (v, e_unioned) in Hpres
                  by (rewrite <- Hu; reflexivity).
                cbn in Hpres.
                (* Hren applies — but we need value via the original i, not put *)
                pose proof (Hren _ _ Hin _ Hg) as Hib.
                exact Hib.
              + intros Heq. subst b.
                pose proof (Hsubdom _ _ Hin) as Hkb.
                apply Hk_xnew_e0_none. exact Hkb. }
          { (* subdom for (x, x_new)::sub0 in e_unioned *)
            intros a b Hin.
            pose proof (union_extends_keys x_new y' e_alloc) as Hpres.
            unfold vc in Hpres.
            replace (union x_new y' e_alloc) with (v, e_unioned) in Hpres
              by (rewrite <- Hu; reflexivity).
            cbn in Hpres.
            destruct Hin as [Heq|Hin].
            - inversion Heq; subst a b. apply Hpres. exact Hk_xnew_a.
            - apply Hpres. apply Hk_pres. apply (Hsubdom _ _ Hin). }
          { exact Hcs'. } }
          (* Now translate Hpost_IH back to the outer goal (extending i not (map.put i x_new dx)) *)
          destruct (clauses_to_instance idx_succ cs ((x, x_new) :: sub0) e_unioned)
            as [pp e_final] eqn:Hci.
          destruct Hpost_IH as (Hok_f & i_final & Hext_f & Hsnd_f).
          split; [exact Hok_f|].
          exists i_final.
          split; [|exact Hsnd_f].
          (* i_final extends map.put i x_new dx, which extends i (since x_new ∉ i) *)
          intros k d Hk.
          apply Hext_f.
          rewrite map.get_put_diff; [exact Hk|].
          intros Heq. subst k. rewrite Hi_xnew_none in Hk. discriminate.
        * (* (miss, miss) — both fresh, alloc_sound × 2 *)
          cbn in Hcs. destruct Hcs as [Hc Hcs'].
          unfold Semantics.eq_sound_for_model in Hc.
          destruct (map.get a_src x) as [dx|] eqn:Hax; cbn in Hc; try tauto.
          destruct (map.get a_src y) as [dy|] eqn:Hay; cbn in Hc; try tauto.
          assert (Hwf_dx : m.(domain_wf symbol) dx).
          { destruct Hm as [HPER _ _ _ _].
            unfold domain_wf. eapply PER_Transitive;
              [eassumption | apply PER_Symmetric; auto]. }
          assert (Hwf_dy : m.(domain_wf symbol) dy).
          { destruct Hm as [HPER _ _ _ _].
            unfold domain_wf. eapply PER_Transitive;
              [apply PER_Symmetric; eassumption | eassumption]. }
          (* First alloc: for x *)
          pose proof (Semantics.alloc_sound idx Eqb_idx Eqb_idx_ok lt idx_succ
                        idx_zero symbol symbol_map idx_map idx_map_ok idx_trie unit m
                        Hlti Hlts Hltt i dx Hwf_dx Hwf_dx) as Halloc_x.
          unfold vc in Halloc_x.
          destruct (alloc idx idx_succ symbol symbol_map idx_map idx_trie unit e0)
            as [x_new e_x] eqn:Halloc_x_eq.
          specialize (Halloc_x e0).
          rewrite Halloc_x_eq in Halloc_x. cbn in Halloc_x.
          destruct Halloc_x as
            (Hok_x & Hsnd_x & Hi_xnew_none & Hk_xnew_e0_none & Hk_xnew_x &
             Hk_pres_x & Hdb_x & Hpar_x & Hwl_x); auto.
          (* Second alloc: for y, on e_x with interpretation (map.put i x_new dx) *)
          pose proof (Semantics.alloc_sound idx Eqb_idx Eqb_idx_ok lt idx_succ
                        idx_zero symbol symbol_map idx_map idx_map_ok idx_trie unit m
                        Hlti Hlts Hltt (map.put i x_new dx) dy Hwf_dy Hwf_dy)
            as Halloc_y.
          unfold vc in Halloc_y.
          destruct (alloc idx idx_succ symbol symbol_map idx_map idx_trie unit e_x)
            as [y_new e_xy] eqn:Halloc_y_eq.
          specialize (Halloc_y e_x).
          rewrite Halloc_y_eq in Halloc_y. cbn in Halloc_y.
          destruct Halloc_y as
            (Hok_y & Hsnd_y & Hi_ynew_none & Hk_ynew_x_none & Hk_ynew_y &
             Hk_pres_y & Hdb_y & Hpar_y & Hwl_y); auto.
          (* Now case-split on whether x = y.  If x = y, the second alloc
             doesn't happen (rename_lookup y after the first alloc hits the
             freshly-added (x, x_new) entry).  If x ≠ y, the second alloc
             allocates y_new for y. *)
          (* Establish Hrm_x : rename_lookup x sub0 e0 = ((x_new, (x, x_new)::sub0), e_x) *)
          assert (Hrm_x : rename_lookup idx Eqb_idx idx_succ symbol symbol_map
                            idx_map idx_trie unit x sub0 e0
                          = ((x_new, (x, x_new)::sub0), e_x)).
          { unfold rename_lookup. rewrite Hx. cbn. rewrite Halloc_x_eq. reflexivity. }
          cbn.
          rewrite Hrm_x. cbn -[Defs.union].
          unfold Basics.compose, rename_lookup at 1.
          (* For (miss, miss), x and y are both fresh in sub0.  Case-split on
             whether x = y.  In the x = y case (reflexive eq_clause x x), the
             second rename_lookup hits (x, x_new) and no further alloc happens. *)
          destruct (eqb x y) eqn:Hxy_eqb.
          { (* x = y case: degenerate; the eq is reflexive after canonicalization *)
            pose proof (Eqb_idx_ok x y) as Hxy_dec.
            rewrite Hxy_eqb in Hxy_dec. subst y.
            (* rename_lookup y (= x) on (x, x_new)::sub0 hits with x_new *)
            assert (Hxx_true : eqb x x = true).
            { pose proof (Eqb_idx_ok x x) as Hxx_dec.
              destruct (eqb x x); [reflexivity|exfalso; apply Hxx_dec; reflexivity]. }
            assert (Hy_hit : named_list_lookup_err ((x, x_new)::sub0) x = Some x_new).
            { cbn. rewrite Hxx_true. reflexivity. }
            rewrite Hy_hit. cbn -[Defs.union find].
            (* Self-union x_new x_new on e_x: fold the inlined find-guts back
               into Defs.union (mirrors the hit/hit case), then discharge via
               the union-preservation lemmas with a reflexive eq_sound. *)
            destruct (@Defs.union idx Eqb_idx symbol symbol_map idx_map idx_trie
                        unit _ x_new x_new e_x) as [v e_unioned] eqn:Hu.
            unfold Defs.union in Hu. cbn in Hu. rewrite Hu. cbn.
            assert (Hpost_IH : let (_, e1) := clauses_to_instance idx_succ cs
                                                ((x, x_new) :: sub0) e_unioned in
                               egraph_ok idx lt symbol symbol_map idx_map idx_trie
                                 unit e1 /\
                               (exists i' : idx_map (domain symbol m),
                                  map.extends i' (map.put i x_new dx) /\
                                  egraph_sound_for_interpretation idx symbol
                                    symbol_map idx_map idx_trie unit m i' e1)).
            { apply IH.
              { pose proof (union_preserves_egraph_ok x_new x_new e_x) as Hpres.
                unfold vc in Hpres.
                replace (union x_new x_new e_x) with (v, e_unioned) in Hpres
                  by (rewrite <- Hu; reflexivity).
                cbn in Hpres. apply Hpres; auto. }
              { pose proof (union_preserves_egraph_sound_for_interpretation
                              m Hm x_new x_new (map.put i x_new dx) e_x) as Hpres.
                unfold vc in Hpres.
                replace (union x_new x_new e_x) with (v, e_unioned) in Hpres
                  by (rewrite <- Hu; reflexivity).
                cbn in Hpres. apply Hpres; auto.
                unfold Semantics.eq_sound_for_model.
                rewrite map.get_put_same. cbn.
                assert (Hdd : dx = dy) by congruence.
                rewrite <- Hdd in Hc. exact Hc. }
              { intros a b Hin d Hg.
                destruct Hin as [Heq|Hin].
                - inversion Heq; subst a b.
                  rewrite map.get_put_same.
                  rewrite Hax in Hg. inversion Hg; subst d. reflexivity.
                - rewrite map.get_put_diff.
                  + exact (Hren _ _ Hin _ Hg).
                  + intros Heq. subst b.
                    pose proof (Hsubdom _ _ Hin) as Hkb.
                    apply Hk_xnew_e0_none. exact Hkb. }
              { intros a b Hin.
                pose proof (union_extends_keys x_new x_new e_x) as Hpres.
                unfold vc in Hpres.
                replace (union x_new x_new e_x) with (v, e_unioned) in Hpres
                  by (rewrite <- Hu; reflexivity).
                cbn in Hpres.
                destruct Hin as [Heq|Hin].
                - inversion Heq; subst a b. apply Hpres. exact Hk_xnew_x.
                - apply Hpres. apply Hk_pres_x. apply (Hsubdom _ _ Hin). }
              { exact Hcs'. } }
            destruct (clauses_to_instance idx_succ cs ((x, x_new) :: sub0) e_unioned)
              as [pp e_final] eqn:Hci.
            destruct Hpost_IH as (Hok_f & i_final & Hext_f & Hsnd_f).
            split; [exact Hok_f|].
            exists i_final.
            split; [|exact Hsnd_f].
            intros k d Hk.
            apply Hext_f.
            rewrite map.get_put_diff; [exact Hk|].
            intros Heq. subst k. rewrite Hi_xnew_none in Hk. discriminate. }
          assert (Hxy_neq : x <> y).
          { intros Heq. pose proof (Eqb_idx_ok x y) as Hxy_dec.
            rewrite Hxy_eqb in Hxy_dec. apply Hxy_dec; auto. }
          assert (Hy_lookup_extended : named_list_lookup_err ((x, x_new) :: sub0) y = None).
          { cbn. case_match.
            - exfalso; apply Hxy_neq.
              pose proof (Eqb_idx_ok y x) as Hyx_dec.
              rewrite case_match_eqn in Hyx_dec.
              symmetry; exact Hyx_dec.
            - exact Hy. }
          rewrite Hy_lookup_extended. cbn -[Defs.union find].
          rewrite Halloc_y_eq. cbn -[Defs.union find].
          (* Union x_new y_new on e_xy *)
          destruct (@Defs.union idx Eqb_idx symbol symbol_map idx_map idx_trie unit _
                       x_new y_new e_xy)
            as [v e_unioned] eqn:Hu.
          unfold Defs.union in Hu. cbn in Hu. rewrite Hu. cbn.
          assert (Hk_xnew_xy : Sep.has_key x_new (parent (equiv e_xy)))
            by (apply Hk_pres_y; exact Hk_xnew_x).
          assert (Hxy_idx_neq : x_new <> y_new).
          { intros Heq. rewrite <- Heq in Hk_ynew_x_none.
            apply Hk_ynew_x_none. exact Hk_xnew_x. }
          assert (Hpost_IH : let (_, e1) := clauses_to_instance idx_succ cs
                                              ((y, y_new) :: (x, x_new) :: sub0) e_unioned in
                             egraph_ok idx lt symbol symbol_map idx_map idx_trie
                               unit e1 /\
                             (exists i' : idx_map (domain symbol m),
                                map.extends i' (map.put (map.put i x_new dx) y_new dy) /\
                                egraph_sound_for_interpretation idx symbol
                                  symbol_map idx_map idx_trie unit m i' e1)).
          { apply IH.
            { pose proof (union_preserves_egraph_ok x_new y_new e_xy) as Hpres.
              unfold vc in Hpres.
              replace (union x_new y_new e_xy) with (v, e_unioned) in Hpres
                by (rewrite <- Hu; reflexivity).
              cbn in Hpres. apply Hpres; auto. }
            { pose proof (union_preserves_egraph_sound_for_interpretation
                            m Hm x_new y_new (map.put (map.put i x_new dx) y_new dy)
                            e_xy) as Hpres.
              unfold vc in Hpres.
              replace (union x_new y_new e_xy) with (v, e_unioned) in Hpres
                by (rewrite <- Hu; reflexivity).
              cbn in Hpres. apply Hpres; auto.
              unfold Semantics.eq_sound_for_model.
              rewrite (map.get_put_diff _ _ _ _ Hxy_idx_neq).
              rewrite map.get_put_same. cbn.
              rewrite map.get_put_same. cbn. exact Hc. }
            { intros a b Hin d Hg.
              destruct Hin as [Heq|Hin].
              - inversion Heq; subst a b.
                rewrite map.get_put_same.
                rewrite Hay in Hg. inversion Hg; subst d. reflexivity.
              - destruct Hin as [Heq|Hin].
                + inversion Heq; subst a b.
                  rewrite (map.get_put_diff _ _ _ _ Hxy_idx_neq).
                  rewrite map.get_put_same.
                  rewrite Hax in Hg. inversion Hg; subst d. reflexivity.
                + assert (Hb_ne_ynew : b <> y_new).
                  { intros Heq; subst b.
                    pose proof (Hsubdom _ _ Hin) as Hkb.
                    apply Hk_ynew_x_none. apply Hk_pres_x. exact Hkb. }
                  assert (Hb_ne_xnew : b <> x_new).
                  { intros Heq; subst b.
                    pose proof (Hsubdom _ _ Hin) as Hkb.
                    apply Hk_xnew_e0_none. exact Hkb. }
                  rewrite (map.get_put_diff _ _ _ _ Hb_ne_ynew).
                  rewrite (map.get_put_diff _ _ _ _ Hb_ne_xnew).
                  exact (Hren _ _ Hin _ Hg). }
            { intros a b Hin.
              pose proof (union_extends_keys x_new y_new e_xy) as Hpres.
              unfold vc in Hpres.
              replace (union x_new y_new e_xy) with (v, e_unioned) in Hpres
                by (rewrite <- Hu; reflexivity).
              cbn in Hpres.
              destruct Hin as [Heq|Hin].
              - inversion Heq; subst a b. apply Hpres. exact Hk_ynew_y.
              - destruct Hin as [Heq|Hin].
                + inversion Heq; subst a b. apply Hpres. exact Hk_xnew_xy.
                + apply Hpres. apply Hk_pres_y. apply Hk_pres_x.
                  apply (Hsubdom _ _ Hin). }
            { exact Hcs'. } }
          destruct (clauses_to_instance idx_succ cs ((y, y_new) :: (x, x_new) :: sub0) e_unioned)
            as [pp e_final] eqn:Hci.
          destruct Hpost_IH as (Hok_f & i_final & Hext_f & Hsnd_f).
          split; [exact Hok_f|].
          exists i_final.
          split; [|exact Hsnd_f].
          intros k d Hk.
          apply Hext_f.
          assert (Hyx_idx_neq : y_new <> x_new) by (intros Heq; apply Hxy_idx_neq; symmetry; exact Heq).
          assert (Hi_ynew_orig : map.get i y_new = None).
          { rewrite map.get_put_diff in Hi_ynew_none.
            - exact Hi_ynew_none.
            - exact Hyx_idx_neq. }
          rewrite map.get_put_diff.
          2: { intros Heq. subst k. rewrite Hi_ynew_orig in Hk. discriminate. }
          rewrite map.get_put_diff; [exact Hk|].
          intros Heq. subst k. rewrite Hi_xnew_none in Hk. discriminate.
      + (* atom_clause: rename_atom + update_entry_sound + IH. *)
        destruct a as [f args out].
        cbn [all] in Hcs.
        destruct Hcs as [Hatom Hcs'].
        unfold Semantics.clause_sound_for_model, Semantics.atom_sound_for_model in Hatom.
        cbn [atom_args atom_ret atom_fn] in Hatom.
        destruct (list_Mmap (map.get a_src) args) as [arg_doms|] eqn:Hargs_src;
          cbn [Is_Some_satisfying] in Hatom; [|tauto].
        destruct (map.get a_src out) as [out_dom|] eqn:Hout_src;
          cbn [Is_Some_satisfying] in Hatom; [|tauto].
        pose proof (@interprets_to_implies_wf_args symbol m Hm f arg_doms out_dom Hatom)
          as Hwf_args.
        pose proof (@interprets_to_implies_wf_conclusion symbol m Hm f arg_doms out_dom Hatom)
          as Hwf_out.
        unfold rename_atom.
        cbn -[rename_lookup list_Mmap update_entry].
        pose proof (list_Mmap_rename_lookup_sound Hlti Hlts Hltt m Hm a_src args arg_doms
                      sub0 e0 i Hok Hsnd Hren Hsubdom Hargs_src Hwf_args) as Hlm_args.
        destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                    idx_trie unit) args sub0 e0) as [ [args' sub1] e1 ] eqn:Hlma.
        destruct Hlm_args as (i1 & Hext1 & Hok1 & Hsnd1 & Hren1 & Hsubdom1 & Hargs'1 &
                              Hall_args'1 & Hmono1).
        cbn [uncurry Basics.compose].
        pose proof (rename_lookup_sound Hlti Hlts Hltt m Hm a_src out out_dom sub1 e1 i1
                      Hok1 Hsnd1 Hren1 Hsubdom1 Hout_src Hwf_out) as Hrl_out.
        destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                    unit out sub1 e1) as [ [out' sub2] e2 ] eqn:Hrlo.
        destruct Hrl_out as (i2 & Hext2 & Hok2 & Hsnd2 & Hren2 & Hsubdom2 & Hi2out' &
                             Hkout'2 & Hmono2).
        cbn [uncurry].
        unfold Basics.compose.
        rewrite Hrlo.
        cbn [uncurry].
        destruct (update_entry {| atom_fn := f; atom_args := args'; atom_ret := out' |} e2)
          as [u e3] eqn:Hue_eq.
        cbn [uncurry].
        pose proof (@update_entry_sound idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero
                      symbol Eqb_symbol Eqb_symbol_ok symbol_map symbol_map_ok
                      idx_map idx_map_ok idx_trie idx_trie_ok unit _ m Hm i2
                      {| atom_fn := f; atom_args := args'; atom_ret := out' |}) as Hue.
        unfold vc in Hue.
        specialize (Hue e2).
        rewrite Hue_eq in Hue.
        cbn [snd atom_args atom_ret atom_fn] in Hue.
        assert (Hargs'2 : list_Mmap (map.get i2) args' = Some arg_doms).
        { clear -Hargs'1 Hext2.
          revert arg_doms Hargs'1.
          induction args' as [|aa aas IHa]; intros ad Hm0;
            cbn [list_Mmap] in Hm0 |- *.
          - exact Hm0.
          - destruct (map.get i1 aa) as [da|] eqn:Haa;
              cbn [Mbind option_monad] in Hm0; [|discriminate].
            rewrite (Hext2 _ _ Haa). cbn [Mbind option_monad].
            destruct (list_Mmap (map.get i1) aas) as [dss|] eqn:Haas;
              cbn [Mbind option_monad] in Hm0; [|discriminate].
            rewrite (IHa dss eq_refl). exact Hm0. }
        assert (Hatom2 : atom_sound_for_model idx symbol idx_map m i2
                           {| atom_fn := f; atom_args := args'; atom_ret := out' |}).
        { unfold Semantics.atom_sound_for_model. cbn [atom_args atom_ret atom_fn].
          rewrite Hargs'2. cbn [Is_Some_satisfying].
          rewrite Hi2out'. cbn [Is_Some_satisfying].
          exact Hatom. }
        specialize (Hue Hok2 Hsnd2
                     ltac:(intros x Hx; apply Hmono2;
                           exact (in_all (fun x' => Sep.has_key x' (parent (equiv e1)))
                                    args' x Hall_args'1 Hx))
                     Hkout'2 Hatom2).
        destruct Hue as (Hok3 & Hsnd3 & Hmono3).
        pose proof (IH sub2 e3 i2 Hok3 Hsnd3 Hren2
                     ltac:(intros x0 y0 Hin; apply Hmono3; exact (Hsubdom2 _ _ Hin)) Hcs')
          as HIH.
        destruct (clauses_to_instance idx_succ cs sub2 e3) as [pp e_final] eqn:Hci.
        destruct HIH as (Hok_f & i_final & Hext_f & Hsnd_f).
        split; [exact Hok_f|].
        exists i_final.
        split; [|exact Hsnd_f].
        intros k v Hk. apply Hext_f. apply Hext2. apply Hext1. exact Hk.
  Qed.

  (* ============================================================== *)
  (* clauses_to_instance_db_monotone: db only grows, never shrinks  *)
  (* ============================================================== *)

  Local Lemma alloc_preserves_db_val
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    db (snd (alloc idx idx_succ symbol symbol_map idx_map idx_trie unit e0)) = db e0.
  Proof.
    unfold alloc.
    destruct (UnionFind.alloc idx (idx_map idx) (idx_map nat) idx_succ (equiv e0))
      as [eq' xf] eqn:Heq.
    cbn [snd db]. reflexivity.
  Qed.

  Local Lemma find_preserves_db_val (x : idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    db (snd (Defs.find x e0)) = db e0.
  Proof.
    unfold Defs.find.
    destruct (UnionFind.find (equiv e0) x) as [uf' v'] eqn:Hf.
    cbn [snd db]. reflexivity.
  Qed.

  Local Lemma union_preserves_db_val (x y : idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    db (snd (Defs.union x y e0)) = db e0.
  Proof.
    unfold Defs.union.
    cbn [Mbind StateMonad.state_monad].
    destruct (Defs.find x e0) as [cx e1] eqn:Hf1.
    cbn [fst snd].
    pose proof (find_preserves_db_val x e0) as Hdb1.
    rewrite Hf1 in Hdb1. cbn [snd] in Hdb1.
    destruct (Defs.find y e1) as [cy e2] eqn:Hf2.
    cbn [fst snd].
    pose proof (find_preserves_db_val y e1) as Hdb2.
    rewrite Hf2 in Hdb2. cbn [snd] in Hdb2.
    eqb_case cx cy.
    - cbn [Mret StateMonad.state_monad snd db]. congruence.
    - cbn [snd db].
      destruct (UnionFind.union idx Eqb_idx (idx_map idx) (idx_map nat) (equiv e2) cx cy)
        as [uf' v'] eqn:Hu.
      cbn [snd db].
      destruct (eqb cx v'); cbn [snd db]; congruence.
  Qed.

  Local Lemma rename_lookup_preserves_db (x : idx) (sub0 : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    db (snd (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                    unit x sub0 e0)) = db e0.
  Proof.
    unfold rename_lookup.
    destruct (named_list_lookup_err sub0 x) as [y|] eqn:Hlook.
    - cbn [Mret StateMonad.state_monad snd db]. reflexivity.
    - cbn [Mbind StateMonad.state_monad].
      destruct (alloc idx idx_succ symbol symbol_map idx_map idx_trie unit e0)
        as [y e1] eqn:Halloc.
      cbn [fst snd].
      pose proof (alloc_preserves_db_val e0) as Hdb1.
      rewrite Halloc in Hdb1. cbn [snd] in Hdb1.
      exact Hdb1.
  Qed.

  Local Lemma list_Mmap_rename_lookup_preserves_db (args : list idx) :
    forall (sub0 : named_list idx idx)
      (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit),
    db (snd (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                          idx_trie unit) args sub0 e0)) = db e0.
  Proof.
    induction args as [|a args IH]; intros sub0 e0.
    - cbn. reflexivity.
    - cbn [list_Mmap].
      destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                  unit a sub0 e0) as [p e1] eqn:Hrla.
      destruct p as [a' sub1].
      destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                             idx_trie unit) args sub1 e1) as [p2 e2] eqn:Hrec.
      pose proof (rename_lookup_preserves_db a sub0 e0) as Hdb1.
      rewrite Hrla in Hdb1. cbn [snd] in Hdb1.
      pose proof (IH sub1 e1) as Hdb2.
      rewrite Hrec in Hdb2. cbn [snd] in Hdb2.
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
      cbn beta iota. unfold Basics.compose.
      rewrite Hrla. cbn [fst snd uncurry].
      destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                             idx_trie unit) args sub1 e1) as [q e3] eqn:Hq.
      destruct q as [args2 sub2]. cbn [snd uncurry db].
      injection Hrec as <- <-. congruence.
  Qed.

  Local Lemma rename_atom_preserves_db (a : atom)
    (sub0 : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    db (snd (rename_atom idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
               unit a sub0 e0)) = db e0.
  Proof.
    destruct a as [f args out].
    unfold rename_atom.
    cbn [atom_fn atom_args atom_ret].
    cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
    cbn beta iota. unfold Basics.compose.
    destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                           idx_trie unit) args sub0 e0)
      as [q1 e1] eqn:Hq1.
    destruct q1 as [args' sub1].
    cbn [fst snd uncurry].
    destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                unit out sub1 e1)
      as [q2 e2] eqn:Hq2.
    destruct q2 as [ret' sub2].
    cbn [snd db uncurry].
    pose proof (list_Mmap_rename_lookup_preserves_db args sub0 e0) as Hdb1.
    pose proof (rename_lookup_preserves_db out sub1 e1) as Hdb2.
    set (LM := list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                            idx_trie unit) args sub0 e0) in *.
    rewrite Hq1 in Hdb1. cbn [snd] in Hdb1.
    set (RL := rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit
                 out sub1 e1) in *.
    rewrite Hq2 in Hdb2. cbn [snd] in Hdb2.
    congruence.
  Qed.

  Local Lemma atom_in_db_after_db_set' (a : atom) (out_a : unit) (b : atom)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    atom_in_db b (db e0) ->
    (b.(atom_fn) <> a.(atom_fn) \/ b.(atom_args) <> a.(atom_args)) ->
    atom_in_db b (db (snd (db_set' idx Eqb_idx symbol symbol_map idx_map idx_trie
                              unit a out_a e0))).
  Proof.
    intros Hb Hneq.
    unfold db_set'. cbn [snd db].
    unfold map_update, atom_in_db, Is_Some_satisfying.
    cbn [atom_fn atom_args atom_ret].
    destruct b as [bfn bargs bret].
    cbn [atom_fn atom_args atom_ret] in Hb, Hneq.
    destruct (map.get (db e0) (atom_fn a)) as [tbl|] eqn:Htbl.
    - eqb_case bfn (atom_fn a).
      + rewrite map.get_put_same. cbn [Is_Some_satisfying].
        unfold atom_in_db, Is_Some_satisfying in Hb. cbn [atom_fn] in Hb.
        rewrite Htbl in Hb. cbn in Hb.
        destruct Hneq as [H|H]; [contradiction H; reflexivity|].
        rewrite map.get_put_diff by auto. exact Hb.
      + rewrite map.get_put_diff by auto.
        unfold atom_in_db, Is_Some_satisfying in Hb. exact Hb.
    - eqb_case bfn (atom_fn a).
      + rewrite map.get_put_same. cbn [Is_Some_satisfying].
        unfold atom_in_db, Is_Some_satisfying in Hb. cbn [atom_fn] in Hb.
        rewrite Htbl in Hb. cbn in Hb. destruct Hb.
      + rewrite map.get_put_diff by auto.
        unfold atom_in_db, Is_Some_satisfying in Hb. exact Hb.
  Qed.

  Local Lemma atom_in_db_lookup_none_neq (a' b : atom)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    atom_in_db b (db e0) ->
    Defs.db_lookup idx symbol symbol_map idx_map idx_trie unit
              a'.(atom_fn) a'.(atom_args) e0 = (None, e0) ->
    b.(atom_fn) <> a'.(atom_fn) \/ b.(atom_args) <> a'.(atom_args).
  Proof.
    intros Hb Hlook.
    unfold Defs.db_lookup in Hlook. cbn in Hlook.
    injection Hlook as Hlook.
    unfold atom_in_db, Is_Some_satisfying in Hb.
    destruct (map.get (db e0) (atom_fn b)) as [tbl_b|] eqn:Htbl_b;
      cbn in Hb; try destruct Hb.
    destruct (map.get tbl_b (atom_args b)) as [r_b|] eqn:Hr_b;
      cbn in Hb; try destruct Hb.
    destruct (map.get (db e0) (atom_fn a')) as [tbl_a|] eqn:Htbl_a.
    - cbn in Hlook.
      destruct (map.get tbl_a (atom_args a')) as [r_a|] eqn:Hr_a.
      + cbn in Hlook. discriminate Hlook.
      + eqb_case (atom_fn b) (atom_fn a').
        * right. intros Hargs_eq.
          rewrite H in Htbl_b. rewrite Htbl_a in Htbl_b.
          injection Htbl_b as Htbl_eq. subst tbl_b.
          rewrite <- Hargs_eq in Hr_a. rewrite Hr_a in Hr_b. discriminate Hr_b.
        * left. assumption.
    - cbn in Hlook.
      left.
      intros Hfn_eq.
      rewrite <- Hfn_eq in Htbl_a. rewrite Htbl_a in Htbl_b. discriminate Htbl_b.
  Qed.

  Local Lemma update_analyses_preserves_db (x : idx) (v : unit)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    db (snd (Defs.update_analyses idx symbol symbol_map idx_map idx_trie unit x v e0))
    = db e0.
  Proof.
    unfold Defs.update_analyses. cbn [snd db]. reflexivity.
  Qed.

  Local Lemma get_analysis_preserves_db (x : idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    db (snd (get_analysis idx symbol symbol_map idx_map idx_trie unit x e0)) = db e0.
  Proof.
    unfold get_analysis.
    destruct (map.get (analyses e0) x) as [a|] eqn:Ha.
    - cbn [snd db]. reflexivity.
    - unfold Mseq.
      cbn [Mbind Mret StateMonad.state_monad fst snd].
      unfold Defs.update_analyses, Defs.push_worklist.
      cbn [snd db]. reflexivity.
  Qed.

  Local Lemma list_Mmap_get_analysis_preserves_db (args : list idx) :
    forall (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit),
    db (snd (list_Mmap (get_analysis idx symbol symbol_map idx_map idx_trie unit)
                       args e0)) = db e0.
  Proof.
    induction args as [|a args IH]; intros e0.
    - cbn [list_Mmap Mret StateMonad.state_monad snd db]. reflexivity.
    - cbn [list_Mmap].
      destruct (get_analysis idx symbol symbol_map idx_map idx_trie unit a e0)
        as [p e1] eqn:Hga.
      cbn [fst snd].
      pose proof (get_analysis_preserves_db a e0) as Hdb1.
      rewrite Hga in Hdb1. cbn [snd] in Hdb1.
      destruct (list_Mmap (get_analysis idx symbol symbol_map idx_map idx_trie unit)
                          args e1) as [p2 e2] eqn:Hrec.
      pose proof (IH e1) as Hdb2.
      rewrite Hrec in Hdb2. cbn [snd] in Hdb2.
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
      cbn beta iota. unfold Basics.compose.
      rewrite Hga. cbn [fst snd].
      destruct (list_Mmap (get_analysis idx symbol symbol_map idx_map idx_trie unit)
                          args e1) as [q e3] eqn:Hq.
      cbn [snd]. injection Hrec as <- <-. congruence.
  Qed.

  Local Lemma db_set_preserves_atom_in_db (a' b : atom)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    atom_in_db b (db e0) ->
    Defs.db_lookup idx symbol symbol_map idx_map idx_trie unit
              a'.(atom_fn) a'.(atom_args) e0 = (None, e0) ->
    atom_in_db b (db (snd (Defs.db_set idx Eqb_idx symbol symbol_map idx_map idx_trie
                              unit a' e0))).
  Proof.
    intros Hb Hlook.
    pose proof (atom_in_db_lookup_none_neq a' b e0 Hb Hlook) as Hneq.
    unfold Defs.db_set.
    cbn [Mbind StateMonad.state_monad].
    unfold Defs.get_analyses.
    destruct (list_Mmap (get_analysis idx symbol symbol_map idx_map idx_trie unit)
                        (atom_args a') e0) as [p e1] eqn:Hga.
    cbn [fst snd].
    pose proof (list_Mmap_get_analysis_preserves_db (atom_args a') e0) as Hdb1.
    rewrite Hga in Hdb1. cbn [snd] in Hdb1.
    destruct (update_analyses idx symbol symbol_map idx_map idx_trie unit
                (atom_ret a') (analyze idx symbol unit a' p) e1)
      as [pu e2] eqn:Hua.
    pose proof (update_analyses_preserves_db (atom_ret a')
                  (analyze idx symbol unit a' p) e1) as Hdb2.
    rewrite Hua in Hdb2. cbn [snd] in Hdb2.
    cbn [snd].
    apply atom_in_db_after_db_set'.
    - rewrite Hdb2. rewrite Hdb1. exact Hb.
    - exact Hneq.
  Qed.

  Local Lemma update_entry_preserves_atom_in_db (a' b : atom)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    atom_in_db b (db e0) ->
    atom_in_db b (db (snd (update_entry a' e0))).
  Proof.
    intros Hb.
    unfold update_entry.
    unfold Mbind, StateMonad.state_monad.
    destruct (Defs.db_lookup idx symbol symbol_map idx_map idx_trie unit
                (atom_fn a') (atom_args a') e0) as [mout e1] eqn:Hlook.
    cbn [fst snd].
    assert (He1 : e1 = e0).
    { unfold Defs.db_lookup in Hlook. cbn in Hlook. injection Hlook as _ He1.
      exact (eq_sym He1). }
    subst e1.
    destruct mout as [r|].
    - unfold Mseq.
      cbn [Mbind StateMonad.state_monad Mret fst snd].
      pose proof (union_preserves_db_val r (atom_ret a') e0) as Hdb.
      set (U := Defs.union r (atom_ret a') e0) in *.
      destruct U as [v u] eqn:Hu.
      cbn [snd] in Hdb.
      cbn [snd]. rewrite Hdb. exact Hb.
    - cbn [Mret StateMonad.state_monad fst snd].
      apply db_set_preserves_atom_in_db.
      + exact Hb.
      + unfold Defs.db_lookup. cbn.
        exact Hlook.
  Qed.

  Lemma map_inj_eq {A B : Type} (f : A -> B) (l1 l2 : list A) :
    (forall x1 x2, In x1 l1 -> In x2 l2 -> f x1 = f x2 -> x1 = x2) ->
    map f l1 = map f l2 -> l1 = l2.
  Proof.
    revert l2.
    induction l1 as [|h1 t1 IH]; intros l2 Hinj Hmap.
    - destruct l2 as [|h2 t2].
      + reflexivity.
      + cbn in Hmap. discriminate Hmap.
    - destruct l2 as [|h2 t2].
      + cbn in Hmap. discriminate Hmap.
      + cbn in Hmap. injection Hmap as Hhead Htail.
        assert (Hh : h1 = h2).
        { apply Hinj; [left; reflexivity | left; reflexivity | exact Hhead]. }
        subst h2.
        f_equal.
        apply IH.
        * intros x1 x2 Hx1 Hx2 Hfx.
          apply (Hinj x1 x2); [right; exact Hx1 | right; exact Hx2 | exact Hfx].
        * exact Htail.
  Qed.

  Lemma named_list_lookup_err_to_lookup (d : idx) (l : named_list idx idx) (x y : idx) :
    named_list_lookup_err l x = Some y -> named_list_lookup d l x = y.
  Proof.
    induction l as [| [s v] l' IH]; intros Herr.
    - cbn in Herr. discriminate Herr.
    - cbn in Herr. cbn.
      destruct (eqb x s) eqn:Heqb.
      + injection Herr as <-. reflexivity.
      + apply IH. exact Herr.
  Qed.

  Local Lemma db_set_adds_atom (a : atom)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    atom_in_db a
      (db (snd (Defs.db_set idx Eqb_idx symbol symbol_map idx_map idx_trie unit a e0))).
  Proof.
    unfold Defs.db_set.
    cbn [Mbind StateMonad.state_monad].
    unfold Defs.get_analyses.
    destruct (list_Mmap (get_analysis idx symbol symbol_map idx_map idx_trie unit)
                        (atom_args a) e0) as [p e1] eqn:Hga.
    cbn [fst snd].
    pose proof (list_Mmap_get_analysis_preserves_db (atom_args a) e0) as Hdb1.
    rewrite Hga in Hdb1. cbn [snd] in Hdb1.
    destruct (update_analyses idx symbol symbol_map idx_map idx_trie unit
                (atom_ret a) (analyze idx symbol unit a p) e1)
      as [pu e2] eqn:Hua.
    pose proof (update_analyses_preserves_db (atom_ret a)
                  (analyze idx symbol unit a p) e1) as Hdb2.
    rewrite Hua in Hdb2. cbn [snd] in Hdb2.
    cbn [snd].
    unfold db_set'. cbn [snd db].
    unfold map_update, atom_in_db, Is_Some_satisfying.
    cbn [atom_fn atom_args atom_ret].
    destruct (map.get (db e2) (atom_fn a)) as [tbl|] eqn:Htbl.
    - rewrite map.get_put_same. cbn [Is_Some_satisfying].
      rewrite map.get_put_same. reflexivity.
    - rewrite map.get_put_same. cbn [Is_Some_satisfying].
      rewrite map.get_put_same. reflexivity.
  Qed.

  Local Lemma db_set_atom_in_db_inv (a b : atom)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    atom_in_db b
      (db (snd (Defs.db_set idx Eqb_idx symbol symbol_map idx_map idx_trie unit a e0))) ->
    (atom_fn b = atom_fn a /\ atom_args b = atom_args a /\ atom_ret b = atom_ret a)
    \/ atom_in_db b (db e0).
  Proof.
    unfold Defs.db_set.
    cbn [Mbind StateMonad.state_monad].
    unfold Defs.get_analyses.
    destruct (list_Mmap (get_analysis idx symbol symbol_map idx_map idx_trie unit)
                        (atom_args a) e0) as [p e1] eqn:Hga.
    cbn [fst snd].
    pose proof (list_Mmap_get_analysis_preserves_db (atom_args a) e0) as Hdb1.
    rewrite Hga in Hdb1. cbn [snd] in Hdb1.
    destruct (update_analyses idx symbol symbol_map idx_map idx_trie unit
                (atom_ret a) (analyze idx symbol unit a p) e1)
      as [pu e2] eqn:Hua.
    pose proof (update_analyses_preserves_db (atom_ret a)
                  (analyze idx symbol unit a p) e1) as Hdb2.
    rewrite Hua in Hdb2. cbn [snd] in Hdb2.
    cbn [snd].
    unfold db_set'. cbn [snd db].
    unfold map_update, atom_in_db, Is_Some_satisfying.
    cbn [atom_fn atom_args atom_ret].
    destruct b as [bfn bargs bret].
    cbn [atom_fn atom_args atom_ret].
    rewrite Hdb2. rewrite Hdb1.
    destruct (map.get (db e0) (atom_fn a)) as [tbl|] eqn:Htbl.
    - eqb_case bfn (atom_fn a).
      + rewrite map.get_put_same. cbn [Is_Some_satisfying].
        eqb_case bargs (atom_args a).
        * rewrite map.get_put_same. cbn [entry_value]. intros Hbret.
          auto using eq_sym.
        * rewrite map.get_put_diff by auto.
          intros Hb. right. rewrite Htbl. exact Hb.
      + rewrite map.get_put_diff by auto. intros Hb. right.
        exact Hb.
    - eqb_case bfn (atom_fn a).
      + rewrite map.get_put_same. cbn [Is_Some_satisfying].
        eqb_case bargs (atom_args a).
        * rewrite map.get_put_same. cbn [entry_value]. intros Hbret.
          auto using eq_sym.
        * rewrite map.get_put_diff by auto.
          unfold default. rewrite map.get_empty. cbn [Is_Some_satisfying].
          intros Hb. destruct Hb.
      + rewrite map.get_put_diff by auto. intros Hb. right.
        exact Hb.
  Qed.

  (* ============================================================ *)
  (* Structural (model-free) spec for rename_atom                *)
  (* ============================================================ *)

  (* F0: if list_Mmap (named_list_lookup_err sub) l = Some l',
         then map (named_list_lookup default sub) l = l'. *)
  Lemma list_Mmap_lookup_err_to_map_default (sub : named_list idx idx) (l l' : list idx) :
    list_Mmap (named_list_lookup_err sub) l = Some l' ->
    map (named_list_lookup default sub) l = l'.
  Proof.
    revert l'.
    induction l as [|a l0 IH]; intros l'.
    - cbn. intros H. injection H as <-. reflexivity.
    - cbn [list_Mmap].
      destruct (named_list_lookup_err sub a) as [v|] eqn:Ha; [|discriminate].
      destruct (list_Mmap (named_list_lookup_err sub) l0) as [vs|] eqn:Hrec; [|discriminate].
      intros H. injection H as <-.
      cbn [map].
      rewrite (named_list_lookup_err_to_lookup default sub a v Ha).
      rewrite (IH vs eq_refl).
      reflexivity.
  Qed.

  (* F1: rename_lookup x preserves union_find_ok, injectivity, domain
         of sub, sub-extension, locates x in sub', x' is a key, and
         db/worklist are unchanged. *)
  Lemma rename_lookup_struct
    (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
    (x : idx) (sub : named_list idx idx)
    (e : Defs.instance idx symbol symbol_map idx_map idx_trie unit)
    (roots : list idx) :
    union_find_ok lt (equiv e) roots ->
    (forall a b y, named_list_lookup_err sub a = Some y ->
                   named_list_lookup_err sub b = Some y -> a = b) ->
    (forall a y, named_list_lookup_err sub a = Some y -> Sep.has_key y (parent (equiv e))) ->
    match rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit x sub e with
    | (x', sub', e') =>
        (exists roots', union_find_ok lt (equiv e') roots') /\
        (forall a b y, named_list_lookup_err sub' a = Some y ->
                       named_list_lookup_err sub' b = Some y -> a = b) /\
        (forall a y, named_list_lookup_err sub' a = Some y -> Sep.has_key y (parent (equiv e'))) /\
        (forall a y, named_list_lookup_err sub a = Some y -> named_list_lookup_err sub' a = Some y) /\
        named_list_lookup_err sub' x = Some x' /\
        Sep.has_key x' (parent (equiv e')) /\
        db e' = db e /\
        worklist e' = worklist e /\
        (forall z, Sep.has_key z (parent (equiv e)) -> Sep.has_key z (parent (equiv e')))
    end.
  Proof.
    intros Huf Hinj Hdom.
    unfold rename_lookup.
    destruct (named_list_lookup_err sub x) as [x'|] eqn:Hlook.
    - (* HIT: rename_lookup returns (x', sub, e) *)
      cbn.
      split. { exists roots. exact Huf. }
      split. { exact Hinj. }
      split. { exact Hdom. }
      split. { intros a y Ha. exact Ha. }
      split. { exact Hlook. }
      split. { exact (Hdom x x' Hlook). }
      split. { reflexivity. }
      split. { reflexivity. }
      { intros z Hz. exact Hz. }
    - (* MISS: alloc allocates x_new, returns (x_new, (x,x_new)::sub, e_alloc) *)
      cbn -[alloc].
      destruct (alloc idx idx_succ symbol symbol_map idx_map idx_trie unit e)
        as [x_new e_alloc] eqn:Halloc.
      (* Apply alloc_struct *)
      pose proof (alloc_struct idx Eqb_idx Eqb_idx_ok lt idx_succ
                    symbol symbol_map idx_map idx_map_ok idx_trie unit
                    Hlti Hlts Hltt) as Halloc_st.
      unfold vc in Halloc_st.
      specialize (Halloc_st e).
      rewrite Halloc in Halloc_st.
      cbn [fst snd] in Halloc_st.
      specialize (Halloc_st roots Huf).
      destruct Halloc_st as (Huf_a & Hfresh & Hknew & Hkmono & Hdb & Hpar & Hwl).
      split. { exists (x_new :: roots). exact Huf_a. }
      split.
      { (* Injectivity of (x,x_new)::sub *)
        intros a b y Ha Hb.
        cbn [named_list_lookup_err] in Ha, Hb.
        eqb_case a x.
        - (* a = x, so Ha : Some x_new = Some y, i.e. y = x_new *)
          injection Ha as <-.
          (* Now y is gone, replaced by x_new; Hb : ... = Some x_new *)
          eqb_case b x.
          + (* b = x *) reflexivity.
          + (* b <> x: Hb : named_list_lookup_err sub b = Some x_new *)
            exfalso. apply Hfresh.
            apply (Hdom b x_new Hb).
        - (* a <> x *)
          eqb_case b x.
          + (* b = x, so Hb : Some x_new = Some y, i.e. y = x_new *)
            injection Hb as <-.
            (* Now y is gone, replaced by x_new; Ha : ... = Some x_new *)
            exfalso. apply Hfresh.
            apply (Hdom a x_new Ha).
          + (* b <> x *)
            exact (Hinj a b y Ha Hb). }
      split.
      { (* dom of (x,x_new)::sub w.r.t. e_alloc *)
        intros a y Ha.
        cbn [named_list_lookup_err] in Ha.
        eqb_case a x.
        - injection Ha as <-.
          exact Hknew.
        - exact (Hkmono y (Hdom a y Ha)). }
      split.
      { (* sub-extension: sub -> (x,x_new)::sub *)
        intros a y Ha.
        cbn [named_list_lookup_err].
        eqb_case a x.
        - (* a = x, but named_list_lookup_err sub x = None *)
          subst. rewrite Hlook in Ha. discriminate.
        - exact Ha. }
      split.
      { (* named_list_lookup_err ((x,x_new)::sub) x = Some x_new *)
        cbn [named_list_lookup_err].
        assert (Hxx : eqb x x = true).
        { pose proof (Eqb_idx_ok x x) as H.
          destruct (eqb x x); [reflexivity | exfalso; apply H; reflexivity]. }
        rewrite Hxx. reflexivity. }
      split. { exact Hknew. }
      split. { symmetry. exact Hdb. }
      split. { symmetry. exact Hwl. }
      { exact Hkmono. }
  Qed.

  (* F2: list version of rename_lookup_struct by induction over args. *)
  Lemma list_Mmap_rename_lookup_struct
    (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
    (args : list idx) :
    forall (sub : named_list idx idx)
      (e : Defs.instance idx symbol symbol_map idx_map idx_trie unit)
      (roots : list idx),
    union_find_ok lt (equiv e) roots ->
    (forall a b y, named_list_lookup_err sub a = Some y ->
                   named_list_lookup_err sub b = Some y -> a = b) ->
    (forall a y, named_list_lookup_err sub a = Some y -> Sep.has_key y (parent (equiv e))) ->
    match list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit)
                    args sub e with
    | (args', sub', e') =>
        (exists roots', union_find_ok lt (equiv e') roots') /\
        (forall a b y, named_list_lookup_err sub' a = Some y ->
                       named_list_lookup_err sub' b = Some y -> a = b) /\
        (forall a y, named_list_lookup_err sub' a = Some y -> Sep.has_key y (parent (equiv e'))) /\
        (forall a y, named_list_lookup_err sub a = Some y -> named_list_lookup_err sub' a = Some y) /\
        list_Mmap (named_list_lookup_err sub') args = Some args' /\
        db e' = db e /\
        worklist e' = worklist e /\
        (forall z, Sep.has_key z (parent (equiv e)) -> Sep.has_key z (parent (equiv e')))
    end.
  Proof.
    induction args as [|a args0 IH];
      intros sub e roots Huf Hinj Hdom.
    - (* nil *)
      cbn.
      split. { exists roots. exact Huf. }
      split. { exact Hinj. }
      split. { exact Hdom. }
      split. { intros a y Ha. exact Ha. }
      split. { reflexivity. }
      split. { reflexivity. }
      split. { reflexivity. }
      { intros z Hz. exact Hz. }
    - (* cons a args0 *)
      cbn [list_Mmap].
      pose proof (rename_lookup_struct Hlti Hlts Hltt a sub e roots Huf Hinj Hdom) as Hrl.
      destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit
                  a sub e) as [ [a' sub1] e1 ] eqn:Hrla.
      destruct Hrl as (Huf1_ex & Hinj1 & Hdom1 & Hext1 & Hlook1 & Hka'1 & Hdb1 & Hwl1 & Hmono1).
      destruct Huf1_ex as [roots1 Huf1].
      cbn -[rename_lookup list_Mmap] in *.
      rewrite Hrla.
      cbn [uncurry Basics.compose].
      pose proof (IH sub1 e1 roots1 Huf1 Hinj1 Hdom1) as HIH.
      unfold Basics.compose.
      destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map
                  idx_map idx_trie unit) args0 sub1 e1)
        as [ [args0' sub2] e2 ] eqn:Hlm.
      cbn [uncurry] in HIH |- *.
      destruct HIH as (Huf2_ex & Hinj2 & Hdom2 & Hext2 & Hmap2 & Hdb2 & Hwl2 & Hmono2).
      split. { exact Huf2_ex. }
      split. { exact Hinj2. }
      split. { exact Hdom2. }
      split.
      { (* sub-extension: sub -> sub2 *)
        intros b y Hb.
        exact (Hext2 b y (Hext1 b y Hb)). }
      split.
      { (* list_Mmap (named_list_lookup_err sub2) (a::args0) = Some (a'::args0') *)
        cbn [list_Mmap].
        (* Carry Hlook1: named_list_lookup_err sub1 a = Some a' to sub2 *)
        assert (Ha'_sub2 : named_list_lookup_err sub2 a = Some a')
          by exact (Hext2 a a' Hlook1).
        rewrite Ha'_sub2.
        rewrite Hmap2.
        reflexivity. }
      split. { congruence. }
      split. { congruence. }
      { intros z Hz. exact (Hmono2 z (Hmono1 z Hz)). }
  Qed.

  (* Helper: if list_Mmap (f sub1) args = Some args' and
     forall z y, f sub1 z = Some y -> f sub2 z = Some y,
     then list_Mmap (f sub2) args = Some args'. *)
  Local Lemma list_Mmap_lookup_err_mono
    (sub1 sub2 : named_list idx idx)
    (args args' : list idx) :
    list_Mmap (named_list_lookup_err sub1) args = Some args' ->
    (forall z y, named_list_lookup_err sub1 z = Some y ->
                 named_list_lookup_err sub2 z = Some y) ->
    list_Mmap (named_list_lookup_err sub2) args = Some args'.
  Proof.
    revert args'.
    induction args as [|a l0 IH]; intros args' Hm Hext.
    - cbn in *. exact Hm.
    - cbn [list_Mmap] in *.
      destruct (named_list_lookup_err sub1 a) as [v|] eqn:Ha; [|discriminate].
      destruct (list_Mmap (named_list_lookup_err sub1) l0) as [vs|] eqn:Hrec; [|discriminate].
      injection Hm as <-.
      rewrite (Hext a v Ha).
      rewrite (IH vs eq_refl Hext).
      reflexivity.
  Qed.

  (* Helper: In z args -> list_Mmap (named_list_lookup_err sub) args = Some args'
     -> exists y, named_list_lookup_err sub z = Some y. *)
  Local Lemma list_Mmap_lookup_err_In_some
    (sub : named_list idx idx) (args args' : list idx) (z : idx) :
    In z args ->
    list_Mmap (named_list_lookup_err sub) args = Some args' ->
    exists y, named_list_lookup_err sub z = Some y.
  Proof.
    revert args'.
    induction args as [|a l0 IH]; intros args' Hin Hm.
    - inversion Hin.
    - cbn [list_Mmap] in Hm.
      destruct (named_list_lookup_err sub a) as [v|] eqn:Ha; [|discriminate].
      destruct (list_Mmap (named_list_lookup_err sub) l0) as [vs|] eqn:Hrec; [|discriminate].
      destruct Hin as [<- | Hin].
      + exists v. exact Ha.
      + exact (IH vs Hin eq_refl).
  Qed.

  (* F3: rename_atom gives the full structural spec. *)
  Lemma rename_atom_struct
    (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
    (a : atom) (sub : named_list idx idx)
    (e : Defs.instance idx symbol symbol_map idx_map idx_trie unit)
    (roots : list idx) :
    union_find_ok lt (equiv e) roots ->
    (forall a0 b y, named_list_lookup_err sub a0 = Some y ->
                    named_list_lookup_err sub b = Some y -> a0 = b) ->
    (forall a0 y, named_list_lookup_err sub a0 = Some y -> Sep.has_key y (parent (equiv e))) ->
    match rename_atom idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit a sub e with
    | (a', sub', e') =>
        (exists roots', union_find_ok lt (equiv e') roots') /\
        (forall a0 b y, named_list_lookup_err sub' a0 = Some y ->
                        named_list_lookup_err sub' b = Some y -> a0 = b) /\
        (forall a0 y, named_list_lookup_err sub' a0 = Some y -> Sep.has_key y (parent (equiv e'))) /\
        (forall z y, named_list_lookup_err sub z = Some y -> named_list_lookup_err sub' z = Some y) /\
        atom_fn a' = atom_fn a /\
        atom_args a' = map (named_list_lookup default sub') (atom_args a) /\
        atom_ret a' = named_list_lookup default sub' (atom_ret a) /\
        (forall z, In z (atom_ret a :: atom_args a) ->
                   exists y, named_list_lookup_err sub' z = Some y) /\
        db e' = db e /\
        worklist e' = worklist e /\
        (forall z, Sep.has_key z (parent (equiv e)) -> Sep.has_key z (parent (equiv e')))
    end.
  Proof.
    intros Huf Hinj Hdom.
    destruct a as [f args out].
    unfold rename_atom.
    cbn [atom_fn atom_args atom_ret].
    cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
    cbn beta iota. unfold Basics.compose.
    (* Mirror rename_atom_preserves_db: use set BEFORE pose proof, destruct, rewrite *)
    pose proof (list_Mmap_rename_lookup_struct Hlti Hlts Hltt args sub e roots
                  Huf Hinj Hdom) as HF2.
    set (LM := list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                            idx_trie unit) args sub e) in *.
    destruct LM as [ [args' sub1] e1 ] eqn:Hargs_eq.
    cbn [fst snd] in HF2.
    destruct HF2 as (Huf1_ex & Hinj1 & Hdom1 & Hext1 & Hmap1 & Hdb1 & Hwl1 & Hmono1).
    destruct Huf1_ex as [roots1 Huf1].
    cbn [fst snd uncurry].
    pose proof (rename_lookup_struct Hlti Hlts Hltt out sub1 e1 roots1
                  Huf1 Hinj1 Hdom1) as HF1.
    set (RL := rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                 unit out sub1 e1) in *.
    destruct RL as [ [out' sub2] e2 ] eqn:Hout_eq.
    cbn [fst snd] in HF1.
    destruct HF1 as (Huf2_ex & Hinj2 & Hdom2 & Hext2 & Hlook2 & Hkout & Hdb2 & Hwl2 & Hmono2).
    cbn [fst snd uncurry atom_fn atom_args atom_ret].
    (* Result atom is Build_atom f args' out', sub'=sub2, e'=e2 *)
    split. { exact Huf2_ex. }
    split. { exact Hinj2. }
    split. { exact Hdom2. }
    split.
    { intros z y Hz. exact (Hext2 z y (Hext1 z y Hz)). }
    split. { reflexivity. }
    split.
    { symmetry.
      assert (Hmap2 : list_Mmap (named_list_lookup_err sub2) args = Some args').
      { exact (list_Mmap_lookup_err_mono sub1 sub2 args args' Hmap1 Hext2). }
      exact (list_Mmap_lookup_err_to_map_default sub2 args args' Hmap2). }
    split.
    { symmetry.
      exact (named_list_lookup_err_to_lookup default sub2 out out' Hlook2). }
    split.
    { intros z Hin.
      destruct Hin as [<- | Hin].
      - exists out'. exact Hlook2.
      - assert (Hmap2 : list_Mmap (named_list_lookup_err sub2) args = Some args').
        { exact (list_Mmap_lookup_err_mono sub1 sub2 args args' Hmap1 Hext2). }
        exact (list_Mmap_lookup_err_In_some sub2 args args' z Hin Hmap2). }
    split. { congruence. }
    split. { congruence. }
    { intros z Hz. exact (Hmono2 z (Hmono1 z Hz)). }
  Qed.

  Lemma clauses_to_instance_db_monotone
    (cs : list (Semantics.clause idx symbol))
    (sub0 : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit)
    (a : Defs.atom idx symbol) :
    atom_in_db a (db e0) ->
    atom_in_db a (db (snd (clauses_to_instance idx_succ (analysis_result:=unit) cs sub0 e0))).
  Proof.
    revert sub0 e0.
    induction cs as [|c cs IH]; intros sub0 e0 Ha.
    - cbn. exact Ha.
    - cbn [Semantics.clauses_to_instance list_Miter].
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mseq Mbind Mret].
      cbn beta iota. unfold Basics.compose.
      destruct (add_clause_to_instance idx Eqb_idx idx_succ symbol symbol_map
                  idx_map idx_trie unit c sub0 e0) as [q e1] eqn:Hadd.
      destruct q as [u sub1].
      cbn [snd uncurry].
      apply IH.
      destruct c as [x y | a_clause].
      + (* eq_clause x y *)
        unfold add_clause_to_instance in Hadd.
        cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind]
          in Hadd.
        cbn beta iota in Hadd. unfold Basics.compose in Hadd.
        destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                    unit x sub0 e0) as [p1 e1'] eqn:Hrx.
        destruct p1 as [x' sub1'].
        cbn [fst snd uncurry] in Hadd.
        destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                    unit y sub1' e1') as [p2 e2'] eqn:Hry.
        destruct p2 as [y' sub2'].
        cbn [fst snd uncurry] in Hadd.
        cbn [lift StateMonad.state_monad Mbind Mret fst snd] in Hadd.
        cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mseq Mbind Mret]
          in Hadd.
        cbn beta iota in Hadd. unfold Basics.compose in Hadd.
        destruct (Defs.union x' y' e2') as [v e3'] eqn:Hu.
        cbn [uncurry fst snd] in Hadd.
        injection Hadd as <- <- <-.
        pose proof (rename_lookup_preserves_db x sub0 e0) as Hdb1.
        rewrite Hrx in Hdb1. cbn [snd] in Hdb1.
        pose proof (rename_lookup_preserves_db y sub1' e1') as Hdb2.
        rewrite Hry in Hdb2. cbn [snd] in Hdb2.
        pose proof (union_preserves_db_val x' y' e2') as Hdb3.
        rewrite Hu in Hdb3. cbn [snd] in Hdb3.
        rewrite Hdb3. rewrite Hdb2. rewrite Hdb1. exact Ha.
      + (* atom_clause a_clause *)
        unfold add_clause_to_instance in Hadd.
        cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind]
          in Hadd.
        cbn beta iota in Hadd. unfold Basics.compose in Hadd.
        destruct (rename_atom idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                    unit a_clause sub0 e0) as [p1 e1'] eqn:Hra.
        destruct p1 as [a' sub1'].
        cbn [fst snd uncurry] in Hadd.
        cbn [lift StateMonad.state_monad Mbind Mret fst snd] in Hadd.
        cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mseq Mbind Mret]
          in Hadd.
        cbn beta iota in Hadd. unfold Basics.compose in Hadd.
        destruct (update_entry a' e1') as [u' e2'] eqn:Hue.
        cbn [uncurry fst snd] in Hadd.
        injection Hadd as <- <- <-.
        pose proof (rename_atom_preserves_db a_clause sub0 e0) as Hdb1.
        rewrite Hra in Hdb1. cbn [snd] in Hdb1.
        pose proof (update_entry_preserves_atom_in_db a' a e1') as Hmono.
        rewrite Hue in Hmono. cbn [snd] in Hmono.
        apply Hmono. rewrite Hdb1. exact Ha.
  Qed.

  (* ============================================================== *)
  (* G-series helpers for the no-collision / atoms-in-db induction   *)
  (* ============================================================== *)

  (* G4: map over a list agrees when the substitution agrees on all list
     elements and the first substitution is defined on all of them. *)
  Lemma map_lookup_default_ext (sub sub' : named_list idx idx) (l : list idx) :
    (forall x y, named_list_lookup_err sub x = Some y ->
                 named_list_lookup_err sub' x = Some y) ->
    (forall x, In x l -> exists y, named_list_lookup_err sub x = Some y) ->
    map (named_list_lookup default sub) l = map (named_list_lookup default sub') l.
  Proof.
    intros Hext Hdom.
    induction l as [|x l IH].
    - reflexivity.
    - cbn [map].
      assert (Hex : exists y, named_list_lookup_err sub x = Some y)
        by (apply Hdom; left; reflexivity).
      destruct Hex as [y Hy].
      assert (Hsub : named_list_lookup default sub x = y)
        by (exact (named_list_lookup_err_to_lookup default sub x y Hy)).
      assert (Hsub' : named_list_lookup default sub' x = y).
      { apply named_list_lookup_err_to_lookup. apply Hext. exact Hy. }
      rewrite Hsub, Hsub'.
      f_equal.
      apply IH.
      intros z Hz. apply Hdom. right. exact Hz.
  Qed.

  (* NoDup-map-app: a repeated image under g in an app-list is impossible. *)
  Lemma nodup_map_app_neq {A B : Type} (g : A -> B) (Pl : list A) (a0 a : A) (tl : list A) :
    NoDup (map g (Pl ++ a :: tl)) -> In a0 Pl -> g a0 = g a -> False.
  Proof.
    intros Hnd Hin Heq.
    rewrite map_app in Hnd. cbn [map] in Hnd.
    apply (NoDup_remove_2 (map g Pl) (map g tl) (g a) Hnd).
    apply in_or_app.
    left.
    rewrite <- Heq.
    apply in_map. exact Hin.
  Qed.

  (* G1: if db_lookup returns Some r, then the corresponding atom is in the db. *)
  Local Lemma db_lookup_some_atom_in_db (f : symbol) (args : list idx) (r : idx)
    (e : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    fst (Defs.db_lookup idx symbol symbol_map idx_map idx_trie unit f args e) = Some r ->
    atom_in_db (Build_atom f args r) (db e).
  Proof.
    unfold Defs.db_lookup. cbn [fst].
    intro Hr.
    destruct (map.get (db e) f) as [tbl|] eqn:Htbl.
    - cbn in Hr.
      destruct (map.get tbl args) as [en|] eqn:Hen.
      + cbn in Hr. injection Hr as <-.
        unfold atom_in_db, Semantics.atom_in_db, Is_Some_satisfying.
        cbn [atom_fn atom_args atom_ret].
        rewrite Htbl. cbn [Is_Some_satisfying].
        rewrite Hen. cbn [Is_Some_satisfying]. reflexivity.
      + cbn in Hr. discriminate Hr.
    - cbn in Hr. discriminate Hr.
  Qed.

  (* Sub-helpers for G2 and G3: equiv/worklist preservation through
     update_analyses, get_analysis, and list_Mmap get_analysis. *)

  Local Lemma update_analyses_preserves_equiv (x : idx) (v : unit)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    equiv (snd (Defs.update_analyses idx symbol symbol_map idx_map idx_trie unit x v e0))
    = equiv e0.
  Proof.
    unfold Defs.update_analyses. cbn [snd equiv]. reflexivity.
  Qed.

  Local Lemma get_analysis_preserves_equiv (x : idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    equiv (snd (get_analysis idx symbol symbol_map idx_map idx_trie unit x e0)) = equiv e0.
  Proof.
    unfold get_analysis.
    destruct (map.get (analyses e0) x) as [a|] eqn:Ha.
    - cbn [snd equiv]. reflexivity.
    - unfold Mseq.
      cbn [Mbind Mret StateMonad.state_monad fst snd].
      unfold Defs.update_analyses, Defs.push_worklist.
      cbn [snd equiv]. reflexivity.
  Qed.

  Local Lemma list_Mmap_get_analysis_preserves_equiv (args : list idx) :
    forall (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit),
    equiv (snd (list_Mmap (get_analysis idx symbol symbol_map idx_map idx_trie unit)
                       args e0)) = equiv e0.
  Proof.
    induction args as [|a args IH]; intros e0.
    - cbn [list_Mmap Mret StateMonad.state_monad snd equiv]. reflexivity.
    - cbn [list_Mmap].
      destruct (get_analysis idx symbol symbol_map idx_map idx_trie unit a e0)
        as [p e1] eqn:Hga.
      cbn [fst snd].
      pose proof (get_analysis_preserves_equiv a e0) as Heq1.
      rewrite Hga in Heq1. cbn [snd] in Heq1.
      destruct (list_Mmap (get_analysis idx symbol symbol_map idx_map idx_trie unit)
                          args e1) as [p2 e2] eqn:Hrec.
      pose proof (IH e1) as Heq2.
      rewrite Hrec in Heq2. cbn [snd] in Heq2.
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
      cbn beta iota. unfold Basics.compose.
      rewrite Hga. cbn [fst snd].
      destruct (list_Mmap (get_analysis idx symbol symbol_map idx_map idx_trie unit)
                          args e1) as [q e3] eqn:Hq.
      cbn [snd]. injection Hrec as <- <-. congruence.
  Qed.

  (* G2: db_set leaves the equiv (union-find) field unchanged. *)
  Local Lemma db_set_preserves_equiv (a : atom)
    (e : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    equiv (snd (Defs.db_set idx Eqb_idx symbol symbol_map idx_map idx_trie unit a e)) = equiv e.
  Proof.
    unfold Defs.db_set.
    cbn [Mbind StateMonad.state_monad].
    unfold Defs.get_analyses.
    destruct (list_Mmap (get_analysis idx symbol symbol_map idx_map idx_trie unit)
                        (atom_args a) e) as [p e1] eqn:Hga.
    cbn [fst snd].
    pose proof (list_Mmap_get_analysis_preserves_equiv (atom_args a) e) as Heq1.
    rewrite Hga in Heq1. cbn [snd] in Heq1.
    destruct (Defs.update_analyses idx symbol symbol_map idx_map idx_trie unit
                (atom_ret a) (analyze idx symbol unit a p) e1)
      as [pu e2] eqn:Hua.
    pose proof (update_analyses_preserves_equiv (atom_ret a)
                  (analyze idx symbol unit a p) e1) as Heq2.
    rewrite Hua in Heq2. cbn [snd] in Heq2.
    cbn [snd].
    unfold db_set'. cbn [snd equiv].
    congruence.
  Qed.

  (* Sub-helpers for G3: worklist all-analysis_repair preservation. *)

  Local Lemma update_analyses_preserves_worklist_ar (x : idx) (v : unit)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    all (fun ent => exists j, ent = analysis_repair idx j) (worklist e0) ->
    all (fun ent => exists j, ent = analysis_repair idx j)
        (worklist (snd (Defs.update_analyses idx symbol symbol_map idx_map idx_trie unit x v e0))).
  Proof.
    unfold Defs.update_analyses. cbn [snd worklist]. intro H. exact H.
  Qed.

  Local Lemma get_analysis_preserves_worklist_ar (x : idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    all (fun ent => exists j, ent = analysis_repair idx j) (worklist e0) ->
    all (fun ent => exists j, ent = analysis_repair idx j)
        (worklist (snd (get_analysis idx symbol symbol_map idx_map idx_trie unit x e0))).
  Proof.
    unfold get_analysis.
    destruct (map.get (analyses e0) x) as [a|] eqn:Ha.
    - cbn [snd worklist]. intro H. exact H.
    - unfold Mseq.
      cbn [Mbind Mret StateMonad.state_monad fst snd].
      unfold Defs.update_analyses, Defs.push_worklist.
      cbn [snd worklist].
      intro H.
      cbn [all].
      split.
      + exists x. reflexivity.
      + exact H.
  Qed.

  Local Lemma list_Mmap_get_analysis_preserves_worklist_ar (args : list idx) :
    forall (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit),
    all (fun ent => exists j, ent = analysis_repair idx j) (worklist e0) ->
    all (fun ent => exists j, ent = analysis_repair idx j)
        (worklist (snd (list_Mmap (get_analysis idx symbol symbol_map idx_map idx_trie unit)
                       args e0))).
  Proof.
    induction args as [|a args IH]; intros e0 Hwl.
    - cbn [list_Mmap Mret StateMonad.state_monad snd worklist]. exact Hwl.
    - cbn [list_Mmap].
      destruct (get_analysis idx symbol symbol_map idx_map idx_trie unit a e0)
        as [p e1] eqn:Hga.
      cbn [fst snd].
      pose proof (get_analysis_preserves_worklist_ar a e0 Hwl) as Hwl1.
      rewrite Hga in Hwl1. cbn [snd] in Hwl1.
      destruct (list_Mmap (get_analysis idx symbol symbol_map idx_map idx_trie unit)
                          args e1) as [p2 e2] eqn:Hrec.
      pose proof (IH e1 Hwl1) as Hwl2.
      rewrite Hrec in Hwl2. cbn [snd] in Hwl2.
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
      cbn beta iota. unfold Basics.compose.
      rewrite Hga. cbn [fst snd].
      destruct (list_Mmap (get_analysis idx symbol symbol_map idx_map idx_trie unit)
                          args e1) as [q e3] eqn:Hq.
      cbn [snd]. injection Hrec as <- <-. exact Hwl2.
  Qed.

  (* G3: db_set preserves the "all analysis_repair" invariant on the worklist. *)
  Local Lemma db_set_preserves_worklist_ar (a : atom)
    (e : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    all (fun ent => exists j, ent = analysis_repair idx j) (worklist e) ->
    all (fun ent => exists j, ent = analysis_repair idx j)
        (worklist (snd (Defs.db_set idx Eqb_idx symbol symbol_map idx_map idx_trie unit a e))).
  Proof.
    intro Hwl.
    unfold Defs.db_set.
    cbn [Mbind StateMonad.state_monad].
    unfold Defs.get_analyses.
    destruct (list_Mmap (get_analysis idx symbol symbol_map idx_map idx_trie unit)
                        (atom_args a) e) as [p e1] eqn:Hga.
    cbn [fst snd].
    pose proof (list_Mmap_get_analysis_preserves_worklist_ar (atom_args a) e Hwl) as Hwl1.
    rewrite Hga in Hwl1. cbn [snd] in Hwl1.
    destruct (Defs.update_analyses idx symbol symbol_map idx_map idx_trie unit
                (atom_ret a) (analyze idx symbol unit a p) e1)
      as [pu e2] eqn:Hua.
    pose proof (update_analyses_preserves_worklist_ar (atom_ret a)
                  (analyze idx symbol unit a p) e1 Hwl1) as Hwl2.
    rewrite Hua in Hwl2. cbn [snd] in Hwl2.
    cbn [snd].
    unfold db_set'. cbn [snd worklist].
    exact Hwl2.
  Qed.

  (* Helper: when db_lookup returns None, update_entry = db_set *)
  Local Lemma update_entry_none_eq_db_set (a : atom)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    fst (Defs.db_lookup idx symbol symbol_map idx_map idx_trie unit
           (atom_fn a) (atom_args a) e0) = None ->
    update_entry a e0 =
    Defs.db_set idx Eqb_idx symbol symbol_map idx_map idx_trie unit a e0.
  Proof.
    intro Hnone.
    unfold update_entry, Defs.db_set, Defs.db_lookup, Defs.get_analyses.
    cbn.
    unfold Mbind, StateMonad.state_monad.
    destruct (map.get (db e0) (atom_fn a)) as [tbl|] eqn:Htbl.
    - destruct (map.get tbl (atom_args a)) as [en|] eqn:Hen.
      + exfalso. cbn in Hnone. rewrite Htbl, Hen in Hnone. cbn in Hnone. discriminate Hnone.
      + cbn. reflexivity.
    - cbn. reflexivity.
  Qed.

  Definition rename_inv (Pl : list atom) (sub : named_list idx idx)
    (e : Defs.instance idx symbol symbol_map idx_map idx_trie unit) : Prop :=
    (forall a b y, named_list_lookup_err sub a = Some y ->
                   named_list_lookup_err sub b = Some y -> a = b)
    /\ (forall x y, named_list_lookup_err sub x = Some y -> Sep.has_key y (parent (equiv e)))
    /\ all (fun ent => exists j, ent = analysis_repair idx j) (worklist e)
    /\ (forall f args r, atom_in_db (Build_atom f args r) (db e) ->
          exists a, In a Pl /\ atom_fn a = f
            /\ map (named_list_lookup default sub) (atom_args a) = args
            /\ named_list_lookup default sub (atom_ret a) = r)
    /\ (forall a, In a Pl ->
          atom_in_db (Build_atom (atom_fn a)
            (map (named_list_lookup default sub) (atom_args a))
            (named_list_lookup default sub (atom_ret a))) (db e))
    /\ (forall a, In a Pl -> forall x, In x (atom_ret a :: atom_args a) ->
          exists y, named_list_lookup_err sub x = Some y).

  Lemma clauses_to_instance_atoms_inv
    (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
    (atoms_all : list atom)
    (Huniq : NoDup (map (fun a => (atom_fn a, atom_args a)) atoms_all)) :
    forall (Pl todo : list atom) (sub : named_list idx idx)
      (e : Defs.instance idx symbol symbol_map idx_map idx_trie unit) (roots : list idx),
    atoms_all = Pl ++ todo ->
    union_find_ok lt (equiv e) roots ->
    rename_inv Pl sub e ->
    match clauses_to_instance idx_succ (analysis_result:=unit) (map atom_clause todo) sub e with
    | (_, sub1, e1) =>
        exists roots1, union_find_ok lt (equiv e1) roots1 /\ rename_inv (Pl ++ todo) sub1 e1
    end.
  Proof.
    intros Pl todo. revert Pl.
    induction todo as [|a todo0 IH]; intros Pl sub e roots Hsplit Huf Hinv.
    - (* BASE: todo = [] *)
      cbn [map clauses_to_instance list_Miter Mret StateMonad.state_monad fst snd].
      rewrite app_nil_r.
      exists roots. split; [exact Huf | exact Hinv].
    - (* STEP: todo = a :: todo0 *)
      cbn [map].
      (* Peel one atom_clause through clauses_to_instance *)
      unfold clauses_to_instance. cbn [list_Miter].
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mseq Mbind Mret].
      cbn beta iota. unfold Basics.compose.
      (* Unfold add_clause_to_instance for atom_clause a *)
      unfold Semantics.add_clause_to_instance.
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
      cbn beta iota. unfold Basics.compose.
      (* Destruct rename_atom *)
      destruct (rename_atom idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                  unit a sub e) as [ [ a' sub' ] e' ] eqn:Hra.
      cbn [fst snd uncurry].
      (* Unfold lift *)
      unfold lift.
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mseq Mbind Mret].
      cbn beta iota. unfold Basics.compose.
      (* Destruct update_entry *)
      destruct (update_entry a' e') as [u'' e''] eqn:Hue.
      cbn [fst snd uncurry].
      (* Fold clauses_to_instance for remainder *)
      change (list_Miter
        (fun c : clause =>
         match c with
         | eq_clause x y =>
             fun (x0 : named_list idx idx) (x1 : instance) =>
             let (x2, y0) :=
               rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                 idx_trie unit x x0 x1 in
             uncurry
               (fun (x' : idx) (x3 : named_list idx idx) (x4 : instance) =>
                let (x5, y1) :=
                  rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                    idx_trie unit y x3 x4 in
                uncurry
                  (fun (y' : idx) (x6 : named_list idx idx) (x7 : instance) =>
                   let (x8, y2) :=
                     let (x8, y2) := union x' y' x7 in (x8, x6, y2) in
                   uncurry
                     (fun (_ : idx) (s : named_list idx idx) (s0 : instance) =>
                      (tt, s, s0))
                     x8 y2)
                  x5 y1)
               x2 y0
         | atom_clause a0 =>
             fun (x : named_list idx idx) (x0 : instance) =>
             let (x1, y) :=
               rename_atom idx Eqb_idx idx_succ symbol symbol_map idx_map
                 idx_trie unit a0 x x0 in
             uncurry
               (fun (a'0 : atom) (s : named_list idx idx) (x2 : instance) =>
                let (x3, y0) := update_entry a'0 x2 in (x3, s, y0))
               x1 y
         end)
        (map atom_clause todo0) sub' e'')
      with (clauses_to_instance idx_succ (analysis_result:=unit) (map atom_clause todo0) sub' e'').
      (* Destruct rename_inv *)
      destruct Hinv as (Hinj & Hdom & Hwl & Hrows & Hfwd & Hvars).
      (* Apply rename_atom_struct *)
      pose proof (rename_atom_struct Hlti Hlts Hltt a sub e roots Huf Hinj Hdom) as Hras.
      rewrite Hra in Hras.
      destruct Hras as (Huf'_ex & Hinj' & Hdom' & Hext & Hfn & Hargs & Hret & Hvars_a &
                        Hdbe' & Hwle' & Hmono).
      destruct Huf'_ex as [roots' Huf'].
      (* Establish NoDup constraint for this step *)
      assert (Huniq_step : NoDup (map (fun a0 => (atom_fn a0, atom_args a0)) (Pl ++ a :: todo0))).
      { rewrite <- Hsplit. exact Huniq. }
      (* CHECKPOINT 2: no-collision assert *)
      assert (Hnone : fst (Defs.db_lookup idx symbol symbol_map idx_map idx_trie unit
                              (atom_fn a') (atom_args a') e') = None).
      { destruct (fst (Defs.db_lookup idx symbol symbol_map idx_map idx_trie unit
                          (atom_fn a') (atom_args a') e')) as [r|] eqn:Hlk;
          [exfalso | reflexivity].
        pose proof (db_lookup_some_atom_in_db (atom_fn a') (atom_args a') r e' Hlk) as Hain.
        rewrite Hdbe' in Hain.
        destruct (Hrows (atom_fn a') (atom_args a') r Hain) as
            (a0 & Ha0in & Hf0 & Hargs0 & Hr0).
        assert (Hmap0_ext : map (named_list_lookup default sub) (atom_args a0)
                           = map (named_list_lookup default sub') (atom_args a0)).
        { apply map_lookup_default_ext.
          - exact Hext.
          - intros x Hx. apply (Hvars a0 Ha0in x). right. exact Hx. }
        assert (Hmap0_a' : map (named_list_lookup default sub') (atom_args a0) = atom_args a').
        { rewrite <- Hmap0_ext. exact Hargs0. }
        assert (Hmap_eq : map (named_list_lookup default sub') (atom_args a0)
                        = map (named_list_lookup default sub') (atom_args a)).
        { rewrite Hmap0_a'. rewrite Hargs. reflexivity. }
        assert (Hargseq : atom_args a0 = atom_args a).
        { apply (map_inj_eq (named_list_lookup default sub') (atom_args a0) (atom_args a)).
          - intros x1 x2 Hx1 Hx2 Hfx.
            assert (Hx1_sub : exists y1, named_list_lookup_err sub' x1 = Some y1).
            { destruct (Hvars a0 Ha0in x1 (in_cons _ x1 _ Hx1)) as [y1 Hy1].
              exists y1. exact (Hext x1 y1 Hy1). }
            assert (Hx2_sub : exists y2, named_list_lookup_err sub' x2 = Some y2).
            { apply Hvars_a. right. exact Hx2. }
            destruct Hx1_sub as [y1 Hy1]. destruct Hx2_sub as [y2 Hy2].
            pose proof (named_list_lookup_err_to_lookup default sub' x1 y1 Hy1) as Hld1.
            pose proof (named_list_lookup_err_to_lookup default sub' x2 y2 Hy2) as Hld2.
            rewrite Hld1 in Hfx. rewrite Hld2 in Hfx.
            assert (Hy12 : y1 = y2) by congruence. subst y2.
            exact (Hinj' x1 x2 y1 Hy1 Hy2).
          - exact Hmap_eq. }
        assert (Hfneq : atom_fn a0 = atom_fn a) by congruence.
        exact (nodup_map_app_neq (fun a1 => (atom_fn a1, atom_args a1))
                  Pl a0 a todo0 Huniq_step Ha0in
                  (f_equal2 pair Hfneq Hargseq)). }
      (* update_entry = db_set when lookup = None *)
      assert (He'' : e'' = snd (Defs.db_set idx Eqb_idx symbol symbol_map idx_map idx_trie unit a' e')).
      { pose proof (update_entry_none_eq_db_set a' e' Hnone) as Hue_eq.
        rewrite Hue_eq in Hue. rewrite Hue. reflexivity. }
      (* (Ob1) union_find_ok lt (equiv e'') roots' *)
      assert (Huf'' : union_find_ok lt (equiv e'') roots').
      { rewrite He''. rewrite db_set_preserves_equiv. exact Huf'. }
      (* (Ob2) rename_inv (Pl ++ [a]) sub' e'' *)
      assert (Hinv2 : rename_inv (Pl ++ [a]) sub' e'').
      { unfold rename_inv. repeat split.
        - exact Hinj'.
        - intros x y Hxy. rewrite He''. rewrite db_set_preserves_equiv. exact (Hdom' x y Hxy).
        - rewrite He''. apply db_set_preserves_worklist_ar. rewrite Hwle'. exact Hwl.
        - intros f args r Hin.
          rewrite He'' in Hin. apply db_set_atom_in_db_inv in Hin.
          destruct Hin as [ (Hbf & Hba & Hbr) | Hin ].
          + cbn [atom_fn atom_args atom_ret] in Hbf, Hba, Hbr.
            exists a. split. { apply in_or_app. right. left. reflexivity. }
            split. { congruence. } split. { congruence. } { congruence. }
          + rewrite Hdbe' in Hin.
            destruct (Hrows f args r Hin) as (a0 & Ha0 & Hf0 & Hargs0 & Hr0).
            exists a0. split. { apply in_or_app. left. exact Ha0. }
            split. { exact Hf0. }
            split.
            { rewrite <- (map_lookup_default_ext sub sub' (atom_args a0) Hext
                           (fun x Hx => Hvars a0 Ha0 x (or_intror Hx))).
              exact Hargs0. }
            { destruct (Hvars a0 Ha0 (atom_ret a0) (in_eq _ _)) as [y Hy].
              pose proof (Hext (atom_ret a0) y Hy) as Hy'.
              pose proof (named_list_lookup_err_to_lookup default sub (atom_ret a0) y Hy) as Hld.
              pose proof (named_list_lookup_err_to_lookup default sub' (atom_ret a0) y Hy') as Hld'.
              congruence. }
        - intros a0 Hin0.
          apply in_app_or in Hin0. destruct Hin0 as [Hin0 | Hin0].
          + pose proof (Hfwd a0 Hin0) as Hfwd0.
            assert (Hmap_a0 : map (named_list_lookup default sub) (atom_args a0)
                            = map (named_list_lookup default sub') (atom_args a0)).
            { apply map_lookup_default_ext.
              - exact Hext.
              - intros x Hx. apply (Hvars a0 Hin0 x). right. exact Hx. }
            assert (Hret_a0 : named_list_lookup default sub (atom_ret a0)
                            = named_list_lookup default sub' (atom_ret a0)).
            { destruct (Hvars a0 Hin0 (atom_ret a0) (in_eq _ _)) as [y Hy].
              pose proof (Hext (atom_ret a0) y Hy) as Hy'.
              pose proof (named_list_lookup_err_to_lookup default sub (atom_ret a0) y Hy) as Hld.
              pose proof (named_list_lookup_err_to_lookup default sub' (atom_ret a0) y Hy') as Hld'.
              congruence. }
            assert (Hfwd0' : atom_in_db (Build_atom (atom_fn a0)
                              (map (named_list_lookup default sub') (atom_args a0))
                              (named_list_lookup default sub' (atom_ret a0))) (db e)).
            { rewrite <- Hmap_a0. rewrite <- Hret_a0. exact Hfwd0. }
            rewrite <- Hdbe' in Hfwd0'.
            replace e'' with (snd (update_entry a' e')).
            { apply update_entry_preserves_atom_in_db. exact Hfwd0'. }
            { rewrite Hue. reflexivity. }
          + destruct Hin0 as [<- | Hf]; [| destruct Hf].
            assert (Ha'_eq : Build_atom (atom_fn a)
                               (map (named_list_lookup default sub') (atom_args a))
                               (named_list_lookup default sub' (atom_ret a)) = a').
            { destruct a' as [f' args' ret'].
              cbn [atom_fn atom_args atom_ret] in Hfn, Hargs, Hret.
              rewrite <- Hfn, <- Hargs, <- Hret. reflexivity. }
            rewrite Ha'_eq. rewrite He''. exact (db_set_adds_atom a' e').
        - intros a0 Hin0 x Hx.
          apply in_app_or in Hin0. destruct Hin0 as [Hin0 | Hin0].
          + destruct (Hvars a0 Hin0 x Hx) as [y Hy]. exists y. exact (Hext x y Hy).
          + destruct Hin0 as [<- | Hf]; [| destruct Hf]. exact (Hvars_a x Hx). }
      (* Apply IH *)
      specialize (IH (Pl ++ [a]) sub' e'' roots').
      assert (Hsplit2 : atoms_all = (Pl ++ [a]) ++ todo0).
      { rewrite <- app_assoc. cbn [app]. exact Hsplit. }
      specialize (IH Hsplit2 Huf'' Hinv2).
      rewrite <- app_assoc in IH. cbn [app] in IH.
      exact IH.
  Qed.

  Lemma clauses_to_instance_atoms_no_collision
    (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
    (atoms : list atom)
    (Huniq : NoDup (map (fun a => (atom_fn a, atom_args a)) atoms)) :
    match clauses_to_instance idx_succ (analysis_result:=unit) (map atom_clause atoms)
            [] (Defs.empty_egraph idx_zero unit) with
    | (_, sub1, e1) =>
        all (fun ent => exists j, ent = analysis_repair idx j) (worklist e1)
        /\ (forall a, In a atoms ->
              atom_in_db (Build_atom (atom_fn a)
                (map (named_list_lookup default sub1) (atom_args a))
                (named_list_lookup default sub1 (atom_ret a))) (db e1))
    end.
  Proof.
    pose proof (clauses_to_instance_atoms_inv Hlti Hlts Hltt atoms Huniq
                  [] atoms []
                  (Defs.empty_egraph idx_zero unit : instance)
                  []
                  eq_refl) as Hmain.
    (* Prove union_find_ok lt (equiv empty_egraph) [] *)
    assert (Huf_empty : union_find_ok lt
              (equiv (Defs.empty_egraph idx_zero unit : instance)) []).
    { cbn [Defs.empty_egraph Defs.equiv].
      exact (Semantics.union_find_empty_ok idx lt idx_succ idx_zero idx_map idx_map_ok). }
    (* Prove rename_inv [] [] empty_egraph *)
    assert (Hinv_empty : rename_inv [] []
                (Defs.empty_egraph idx_zero unit : instance)).
    { unfold rename_inv. repeat split.
      - (* injectivity: vacuous, lookup_err [] _ = None *)
        intros a b y H. cbn in H. discriminate H.
      - (* domain: vacuous *)
        intros x y H. cbn in H. discriminate H.
      - (* I-rows: atom_in_db in empty db => False
           Note: worklist conjunct is resolved by repeat split (all _ [] = True) *)
        intros f args r Hin.
        unfold atom_in_db, Semantics.atom_in_db, Is_Some_satisfying in Hin.
        cbn [atom_fn atom_args atom_ret Defs.empty_egraph Defs.db] in Hin.
        rewrite map.get_empty in Hin. cbn in Hin. destruct Hin.
      - (* I-fwd: In a [] => False *)
        intros a Hin. destruct Hin.
      - (* I-vars: In a [] => False *)
        intros a Hin. destruct Hin. }
    specialize (Hmain Huf_empty Hinv_empty).
    cbn [app] in Hmain.
    destruct (clauses_to_instance idx_succ (analysis_result:=unit) (map atom_clause atoms)
                [] (Defs.empty_egraph idx_zero unit : instance)) as [ [ u sub1 ] e1 ].
    destruct Hmain as (roots1 & _ & Hinv1).
    unfold rename_inv in Hinv1.
    destruct Hinv1 as (_ & _ & Hwl1 & _ & Hfwd1 & _).
    split; [exact Hwl1 | exact Hfwd1].
  Qed.

  Lemma in_db_to_atoms_iff_atom_in_db (a : atom) (d : db_map idx symbol symbol_map idx_trie unit) :
    In a (db_to_atoms d) <-> atom_in_db a d.
  Proof.
    unfold Semantics.db_to_atoms, Semantics.atom_in_db.
    rewrite in_flat_map.
    split.
    - intros [ [f tbl] [Hft Hin] ].
      apply Properties.map.tuples_spec in Hft.
      unfold Semantics.table_atoms in Hin.
      rewrite in_map_iff in Hin.
      destruct Hin as [ [k e] [Heq Hke] ].
      apply Properties.map.tuples_spec in Hke.
      unfold Semantics.row_to_atom in Heq; subst a.
      cbn [atom_fn atom_args atom_ret].
      rewrite Hft. cbn [Is_Some_satisfying].
      rewrite Hke. cbn [Is_Some_satisfying]. reflexivity.
    - intros Hin.
      destruct (map.get d a.(atom_fn)) as [tbl|] eqn:Hd;
        cbn [Is_Some_satisfying] in Hin; try tauto.
      destruct (map.get tbl a.(atom_args)) as [r|] eqn:Htbl;
        cbn [Is_Some_satisfying] in Hin; try tauto.
      exists (a.(atom_fn), tbl); split.
      + apply Properties.map.tuples_spec; exact Hd.
      + unfold Semantics.table_atoms.
        rewrite in_map_iff.
        exists (a.(atom_args), r); split.
        * unfold Semantics.row_to_atom. destruct a; cbn in *; subst; reflexivity.
        * apply Properties.map.tuples_spec; exact Htbl.
  Qed.

  Lemma db_to_atoms_sound (m : model symbol) (i : idx_map (m.(domain symbol)))
      (e : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    Semantics.egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie unit m i e ->
    all (Semantics.clause_sound_for_model idx symbol idx_map m i)
        (map (@atom_clause idx symbol) (db_to_atoms (db e))).
  Proof.
    intros Hsnd.
    apply all_map_in.
    intros a Hin.
    cbn.
    exact (Semantics.atom_interpretation _ _ _ _ _ _ _ _ _ Hsnd a
      (proj1 (in_db_to_atoms_iff_atom_in_db a (db e)) Hin)).
  Qed.

  Lemma uf_eqs_sound (m : model symbol) (i : idx_map (m.(domain symbol)))
      (e : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    Semantics.egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie unit m i e ->
    all (Semantics.clause_sound_for_model idx symbol idx_map m i)
        (map (fun p => @eq_clause idx symbol (fst p) (snd p))
             (map.tuples (parent (equiv e)))).
  Proof.
    intros Hsnd.
    apply all_map_in.
    intros [x y] Hin.
    cbn.
    apply (Semantics.rel_interpretation _ _ _ _ _ _ _ _ _ Hsnd).
    unfold uf_rel_PER.
    apply PER_clo_base.
    apply Properties.map.tuples_spec in Hin.
    exact Hin.
  Qed.

  (* ============================================================== *)
  (* compile_rule structural facts                                    *)
  (* ============================================================== *)

  (* Helper tactic for the common destructuring pattern *)

  Lemma compile_rule_inl_query_vars_dedup :
    forall rf r st0 er st1,
      compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf r st0 = (inl er, st1) ->
      exists L, query_vars idx symbol er = dedup (eqb (A:=idx)) L.
  Proof.
    intros rf r st0 er st1 Hc.
    unfold compile_rule in Hc.
    destruct (optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie r rf)
      as [p ceqs].
    destruct p as [assumptions catoms].
    set (qvs := dedup (eqb (A:=idx)) (flat_map (atom_fvs idx symbol) assumptions)) in *.
    destruct (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) assumptions st0)
      as [qcls_ptrs st'] eqn:Hmap.
    cbn [Mbind StateMonad.state_monad] in Hc.
    rewrite Hmap in Hc.
    destruct qcls_ptrs as [| c cs].
    - cbn [Mret StateMonad.state_monad] in Hc. inversion Hc.
    - cbn [Mret StateMonad.state_monad] in Hc. inversion Hc; subst.
      exists (flat_map (atom_fvs idx symbol) assumptions).
      reflexivity.
  Qed.

  Lemma compile_rule_inl_write_vars_eq :
    forall rf r st0 er st1,
      compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf r st0 = (inl er, st1) ->
      write_vars idx symbol er =
        clauses_fvs idx Eqb_idx symbol
          (map (uncurry (@eq_clause idx symbol)) (write_unifications idx symbol er)
           ++ map (@atom_clause idx symbol) (write_clauses idx symbol er))
          (query_vars idx symbol er).
  Proof.
    intros rf r st0 er st1 Hc.
    unfold compile_rule in Hc.
    destruct (optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie r rf)
      as [p ceqs].
    destruct p as [assumptions catoms].
    set (qvs := dedup (eqb (A:=idx)) (flat_map (atom_fvs idx symbol) assumptions)) in *.
    destruct (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) assumptions st0)
      as [qcls_ptrs st'] eqn:Hmap.
    cbn [Mbind StateMonad.state_monad] in Hc.
    rewrite Hmap in Hc.
    destruct qcls_ptrs as [| c cs].
    - cbn [Mret StateMonad.state_monad] in Hc. inversion Hc.
    - cbn [Mret StateMonad.state_monad] in Hc. inversion Hc; subst.
      cbn [write_vars query_vars write_unifications write_clauses].
      reflexivity.
  Qed.

  Lemma compile_rule_inl_NoDup_query_vars :
    forall rf r st0 er st1,
      compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf r st0 = (inl er, st1) ->
      NoDup (query_vars idx symbol er).
  Proof.
    intros rf r st0 er st1 Hc.
    unfold compile_rule in Hc.
    destruct (optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie r rf)
      as [p ceqs].
    destruct p as [assumptions catoms].
    set (qvs := dedup (eqb (A:=idx)) (flat_map (atom_fvs idx symbol) assumptions)) in *.
    destruct (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) assumptions st0)
      as [qcls_ptrs st'] eqn:Hmap.
    cbn [Mbind StateMonad.state_monad] in Hc.
    rewrite Hmap in Hc.
    destruct qcls_ptrs as [| c cs].
    - cbn [Mret StateMonad.state_monad] in Hc. inversion Hc.
    - cbn [Mret StateMonad.state_monad] in Hc. inversion Hc; subst.
      cbn [query_vars].
      unfold qvs.
      apply NoDup_dedup.
  Qed.

  Lemma compile_rule_inl_NoDup_write_vars :
    forall rf r st0 er st1,
      compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf r st0 = (inl er, st1) ->
      NoDup (write_vars idx symbol er).
  Proof.
    intros rf r st0 er st1 Hc.
    unfold compile_rule in Hc.
    destruct (optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie r rf)
      as [p ceqs].
    destruct p as [assumptions catoms].
    set (qvs := dedup (eqb (A:=idx)) (flat_map (atom_fvs idx symbol) assumptions)) in *.
    destruct (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) assumptions st0)
      as [qcls_ptrs st'] eqn:Hmap.
    cbn [Mbind StateMonad.state_monad] in Hc.
    rewrite Hmap in Hc.
    destruct qcls_ptrs as [| c cs].
    - cbn [Mret StateMonad.state_monad] in Hc. inversion Hc.
    - cbn [Mret StateMonad.state_monad] in Hc. inversion Hc; subst.
      cbn [write_vars].
      unfold clauses_fvs.
      apply NoDup_filter.
      apply NoDup_dedup.
  Qed.

  Lemma compile_rule_inl_write_query_disjoint :
    forall rf r st0 er st1,
      compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf r st0 = (inl er, st1) ->
      forall x, In x (write_vars idx symbol er) -> ~ In x (query_vars idx symbol er).
  Proof.
    intros rf r st0 er st1 Hc.
    unfold compile_rule in Hc.
    destruct (optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie r rf)
      as [p ceqs].
    destruct p as [assumptions catoms].
    set (qvs := dedup (eqb (A:=idx)) (flat_map (atom_fvs idx symbol) assumptions)) in *.
    destruct (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) assumptions st0)
      as [qcls_ptrs st'] eqn:Hmap.
    cbn [Mbind StateMonad.state_monad] in Hc.
    rewrite Hmap in Hc.
    destruct qcls_ptrs as [| c cs].
    - cbn [Mret StateMonad.state_monad] in Hc. inversion Hc.
    - cbn [Mret StateMonad.state_monad] in Hc. inversion Hc; subst.
      cbn [write_vars query_vars].
      unfold clauses_fvs.
      intros x Hx Hin_qvs.
      apply filter_In in Hx as [_ Hneg].
      apply (@inb_is_In idx Eqb_idx Eqb_idx_ok x qvs) in Hin_qvs.
      rewrite negb_true_iff in Hneg.
      rewrite Hneg in Hin_qvs.
      exact Hin_qvs.
  Qed.

  Lemma compile_rule_inl_write_clauses_cover :
    forall rf r st0 er st1,
      compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf r st0 = (inl er, st1) ->
      forall c, In c (write_clauses idx symbol er) ->
      forall x, In x (c.(atom_ret) :: c.(atom_args)) ->
      In x (query_vars idx symbol er) \/ In x (write_vars idx symbol er).
  Proof.
    intros rf r st0 er st1 Hc.
    unfold compile_rule in Hc.
    destruct (optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie r rf)
      as [p ceqs].
    destruct p as [assumptions catoms].
    set (qvs := dedup (eqb (A:=idx)) (flat_map (atom_fvs idx symbol) assumptions)) in *.
    set (cvars := clauses_fvs idx Eqb_idx symbol
      (map (uncurry (@eq_clause idx symbol)) ceqs ++ map (@atom_clause idx symbol) catoms) qvs) in *.
    destruct (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) assumptions st0)
      as [qcls_ptrs st'] eqn:Hmap.
    cbn [Mbind StateMonad.state_monad] in Hc.
    rewrite Hmap in Hc.
    destruct qcls_ptrs as [| c cs].
    - cbn [Mret StateMonad.state_monad] in Hc. inversion Hc.
    - cbn [Mret StateMonad.state_monad] in Hc. inversion Hc; subst.
      cbn [write_clauses query_vars write_vars].
      intros ac Hac x Hx.
      assert (Hin_flat : In x (flat_map (clause_vars idx symbol)
        (map (uncurry (@eq_clause idx symbol)) ceqs ++ map (@atom_clause idx symbol) catoms))).
      { apply in_flat_map.
        exists (@atom_clause idx symbol ac).
        split.
        - apply in_app_iff. right. apply in_map_iff. exists ac. split; [reflexivity | exact Hac].
        - cbn [clause_vars]. exact Hx. }
      destruct (inb x qvs) eqn:Hq.
      + left.
        apply (@inb_is_In idx Eqb_idx Eqb_idx_ok x qvs).
        rewrite Hq. exact I.
      + right.
        unfold cvars.
        unfold clauses_fvs.
        apply filter_In.
        split.
        * apply (proj1 (@dedup_preserves_In idx eqb (eqb_boolspec idx) _ x)).
          exact Hin_flat.
        * rewrite Hq. reflexivity.
  Qed.

  Lemma compile_rule_inl_write_unifs_cover :
    forall rf r st0 er st1,
      compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf r st0 = (inl er, st1) ->
      forall p, In p (write_unifications idx symbol er) ->
      (In (fst p) (query_vars idx symbol er) \/ In (fst p) (write_vars idx symbol er)) /\
      (In (snd p) (query_vars idx symbol er) \/ In (snd p) (write_vars idx symbol er)).
  Proof.
    intros rf r st0 er st1 Hc.
    unfold compile_rule in Hc.
    destruct (optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie r rf)
      as [pp ceqs].
    destruct pp as [assumptions catoms].
    set (qvs := dedup (eqb (A:=idx)) (flat_map (atom_fvs idx symbol) assumptions)) in *.
    set (cvars := clauses_fvs idx Eqb_idx symbol
      (map (uncurry (@eq_clause idx symbol)) ceqs ++ map (@atom_clause idx symbol) catoms) qvs) in *.
    destruct (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) assumptions st0)
      as [qcls_ptrs st'] eqn:Hmap.
    cbn [Mbind StateMonad.state_monad] in Hc.
    rewrite Hmap in Hc.
    destruct qcls_ptrs as [| c cs].
    - cbn [Mret StateMonad.state_monad] in Hc. inversion Hc.
    - cbn [Mret StateMonad.state_monad] in Hc. inversion Hc; subst.
      cbn [write_unifications query_vars write_vars].
      intros [x y] Hxy.
      cbn [fst snd].
      assert (Hx_flat : In x (flat_map (clause_vars idx symbol)
        (map (uncurry (@eq_clause idx symbol)) ceqs ++ map (@atom_clause idx symbol) catoms))).
      { apply in_flat_map.
        exists (@eq_clause idx symbol x y).
        split.
        - apply in_app_iff. left. apply in_map_iff. exists (x, y). split; [reflexivity | exact Hxy].
        - cbn [clause_vars]. left. reflexivity. }
      assert (Hy_flat : In y (flat_map (clause_vars idx symbol)
        (map (uncurry (@eq_clause idx symbol)) ceqs ++ map (@atom_clause idx symbol) catoms))).
      { apply in_flat_map.
        exists (@eq_clause idx symbol x y).
        split.
        - apply in_app_iff. left. apply in_map_iff. exists (x, y). split; [reflexivity | exact Hxy].
        - cbn [clause_vars]. right. left. reflexivity. }
      split.
      + destruct (inb x qvs) eqn:Hqx.
        * left. apply (@inb_is_In idx Eqb_idx Eqb_idx_ok x qvs). rewrite Hqx. exact I.
        * right. unfold cvars, clauses_fvs. apply filter_In. split.
          { apply (proj1 (@dedup_preserves_In idx eqb (eqb_boolspec idx) _ x)). exact Hx_flat. }
          rewrite Hqx. reflexivity.
      + destruct (inb y qvs) eqn:Hqy.
        * left. apply (@inb_is_In idx Eqb_idx Eqb_idx_ok y qvs). rewrite Hqy. exact I.
        * right. unfold cvars, clauses_fvs. apply filter_In. split.
          { apply (proj1 (@dedup_preserves_In idx eqb (eqb_boolspec idx) _ y)). exact Hy_flat. }
          rewrite Hqy. reflexivity.
  Qed.

  (* ============================================================== *)
  (* Connecting compiled_rules of build_rule_set to compile_rule     *)
  (* ============================================================== *)

  Lemma split_sum_list_in_fst :
    forall (A B : Type) (l : list (A + B)) (a : A),
      In a (fst (split_sum_list l)) <-> In (inl a) l.
  Proof.
    intros A B l a.
    induction l as [|h t IH].
    - cbn. tauto.
    - cbn [split_sum_list List.fold_right].
      destruct h as [a' | b'].
      + cbn [fst In].
        rewrite IH.
        split.
        * intros [Heq | Hin].
          -- left. congruence.
          -- right. exact Hin.
        * intros [Heq | Hin].
          -- left. injection Heq. auto.
          -- right. exact Hin.
      + cbn [fst In].
        rewrite IH.
        split.
        * intros Hin. right. exact Hin.
        * intros [Heq | Hin].
          -- discriminate Heq.
          -- exact Hin.
  Qed.

  Lemma list_Mmap_state_in :
    forall (X S Y : Type) (f : X -> state S Y) (xs : list X) (s0 : S) (y : Y),
      In y (fst (list_Mmap f xs s0)) ->
      exists x s s', In x xs /\ f x s = (y, s').
  Proof.
    intros X S Y f xs.
    induction xs as [|x xs IH].
    - intros s0 y Hin. cbn in Hin. destruct Hin.
    - intros s0 y Hin.
      cbn [list_Mmap Mbind Mret StateMonad.state_monad] in Hin.
      destruct (f x s0) as [y0 s'] eqn:Hf.
      destruct (list_Mmap f xs s') as [ys s''] eqn:Hrec.
      cbn [fst] in Hin.
      cbn [In] in Hin.
      destruct Hin as [Heq | Hin].
      + exists x, s0, s'. split.
        * left. reflexivity.
        * rewrite Hf. congruence.
      + assert (Hin' : In y (fst (list_Mmap f xs s'))).
        { rewrite Hrec. cbn [fst]. exact Hin. }
        apply IH in Hin'.
        destruct Hin' as (x' & s1 & s2 & Hxin & Hfx').
        exists x', s1, s2. split.
        * right. exact Hxin.
        * exact Hfx'.
  Qed.

  Lemma in_compiled_rules_build_rule_set :
    forall (rf : nat) (rules : list sequent)
           (er : erule idx symbol),
      In er (compiled_rules idx symbol symbol_map idx_map
               (build_rule_set idx_succ idx_zero rf rules)) ->
      exists rule st0 st1,
        In rule rules /\
        compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf rule st0 = (inl er, st1).
  Proof.
    intros rf rules er Hin.
    unfold build_rule_set in Hin.
    destruct (list_Mmap (compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf) rules map.empty)
      as [crs cp] eqn:Hlm.
    destruct (split_sum_list crs) as [erules consts] eqn:Hssl.
    cbn [compiled_rules] in Hin.
    assert (Herules : erules = fst (split_sum_list crs)).
    { rewrite Hssl. reflexivity. }
    rewrite Herules in Hin.
    apply split_sum_list_in_fst in Hin.
    assert (Hcrs : crs = fst (list_Mmap (compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf) rules map.empty)).
    { rewrite Hlm. reflexivity. }
    rewrite Hcrs in Hin.
    apply list_Mmap_state_in in Hin.
    destruct Hin as (rule & s & s' & Hrule_in & Hcompile).
    exists rule, s, s'.
    exact (conj Hrule_in Hcompile).
  Qed.

  (* ============================================================== *)
  (* Good sequents                                                    *)
  (* ============================================================== *)

  (* A syntactic condition ruling out sequents the optimiser cannot
     soundly transform.  Process clauses left-to-right, growing a set
     of "seen" vars.  An [atom_clause] is always good.  An
     [eq_clause x y] is good only if at least one of [x], [y] appears
     in a previously-seen good clause.

     The condition ensures every variable in the sequent is "anchored"
     (transitively) to some atom — so the optimiser's [live_eqn] filter
     never drops a semantically-required constraint. *)
  Fixpoint clauses_good (seen : list idx) (cs : list clause) : Prop :=
    match cs with
    | [] => True
    | atom_clause a :: rest =>
        clauses_good (clause_vars idx symbol (atom_clause a) ++ seen) rest
    | eq_clause x y :: rest =>
        (In x seen \/ In y seen)
        /\ clauses_good (clause_vars idx symbol (eq_clause x y) ++ seen) rest
    end.

  (* ============================================================== *)
  (* Items D0/D1: pullback_assignment and soundness helpers         *)
  (* ============================================================== *)

  (* D0: Given an assignment [a_opt] on renamed (target) vars and a
     renaming [sub : named_list idx idx] of source vars to target vars,
     [pullback_assignment] produces the induced assignment on source
     vars: each source var x maps to a_opt's value at x's image y. *)
  Definition pullback_assignment {A} (a_opt : idx_map A) (sub : named_list idx idx)
    : idx_map A :=
    fold_right (fun '(x, y) acc =>
                  match map.get a_opt y with
                  | Some d => map.put acc x d
                  | None => acc
                  end) map.empty sub.

  (* D0 spec: if sub maps x to y and a_opt maps y to d, then
     pullback_assignment maps x to d. *)
  Lemma get_pullback_assignment_some {A} (a_opt : idx_map A) (sub : named_list idx idx)
        (x y : idx) (d : A) :
    named_list_lookup_err sub x = Some y ->
    map.get a_opt y = Some d ->
    map.get (pullback_assignment a_opt sub) x = Some d.
  Proof.
    revert x y d.
    induction sub as [| [x0 y0] sub' IH]; intros x y d Hlook Hopt.
    - cbn in Hlook. discriminate.
    - cbn [pullback_assignment fold_right named_list_lookup_err] in *.
      destruct (eqb x x0) eqn:Hxx0.
      + (* x = x0 *)
        injection Hlook as <-.
        rewrite Hopt.
        pose proof (eqb_spec x x0) as Hspec.
        rewrite Hxx0 in Hspec.
        subst x0.
        rewrite map.get_put_same. reflexivity.
      + (* x <> x0 *)
        destruct (map.get a_opt y0) as [d0|] eqn:Hy0.
        * (* head puts x0 -> d0 *)
          pose proof (eqb_spec x x0) as Hspec.
          rewrite Hxx0 in Hspec.
          rewrite map.get_put_diff by exact Hspec.
          exact (IH x y d Hlook Hopt).
        * (* head does nothing *)
          exact (IH x y d Hlook Hopt).
  Qed.

  (* Helper: if every element of L has a sub-image, and
     list_Mmap (map.get a_opt) (map (named_list_lookup default sub) L) = Some doms,
     then list_Mmap (map.get (pullback_assignment a_opt sub)) L = Some doms. *)
  Lemma list_Mmap_pullback_some {A} (a_opt : idx_map A) (sub : named_list idx idx)
        (L : list idx) :
    forall (doms : list A),
    (forall x, In x L -> exists y, named_list_lookup_err sub x = Some y) ->
    list_Mmap (map.get a_opt) (map (named_list_lookup default sub) L) = Some doms ->
    list_Mmap (map.get (pullback_assignment a_opt sub)) L = Some doms.
  Proof.
    induction L as [| x L' IH]; intros doms Hvars Hmmap.
    - cbn in Hmmap. injection Hmmap as <-. reflexivity.
    - (* Get the sub image for x *)
      destruct (Hvars x (or_introl eq_refl)) as [y Hyx].
      pose proof (named_list_lookup_err_to_lookup default sub x y Hyx) as Hld.
      (* Simplify Hmmap *)
      cbn [map list_Mmap] in Hmmap.
      rewrite Hld in Hmmap.
      destruct (map.get a_opt y) as [d|] eqn:Hdy.
      + destruct (list_Mmap (map.get a_opt) (map (named_list_lookup default sub) L'))
          as [ds|] eqn:Hds.
        * injection Hmmap as <-.
          cbn [list_Mmap].
          rewrite (get_pullback_assignment_some a_opt sub x y d Hyx Hdy).
          rewrite (IH ds (fun z Hz => Hvars z (or_intror Hz)) eq_refl).
          reflexivity.
        * discriminate.
      + discriminate.
  Qed.

  (* M2 (D1): The source atoms, when renamed via sub1, are all in
     e_assum's db; and a_opt is sound on e_assum's atoms. Then
     the pullback assignment is sound on the original source atoms. *)
  Lemma a_src_sound_on_assumptions
        (m : model symbol) (Hm : model_ok symbol m)
        (atoms : list atom) (sub1 : named_list idx idx)
        (a_opt : idx_map (m.(domain symbol)))
        (e_assum : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    (* every source atom's vars (ret + args) are keys of sub1 *)
    (forall a, In a atoms -> forall x, In x (atom_ret a :: atom_args a) ->
         exists y, named_list_lookup_err sub1 x = Some y) ->
    (* every renamed source atom is in db e_assum *)
    (forall a, In a atoms ->
         atom_in_db (Build_atom (atom_fn a)
           (map (named_list_lookup default sub1) (atom_args a))
           (named_list_lookup default sub1 (atom_ret a))) (db e_assum)) ->
    (* a_opt is sound on the read-back atoms of e_assum *)
    all (Semantics.clause_sound_for_model idx symbol idx_map m a_opt)
        (map (@atom_clause idx symbol) (db_to_atoms (db e_assum))) ->
    all (Semantics.clause_sound_for_model idx symbol idx_map m
           (pullback_assignment a_opt sub1))
        (map (@atom_clause idx symbol) atoms).
  Proof.
    intros Hvars Hren_db Hass.
    apply (Semantics.all_map_in (@atom_clause idx symbol)
             (Semantics.clause_sound_for_model idx symbol idx_map m
                (pullback_assignment a_opt sub1))
             atoms).
    intros a Hin_a.
    cbn [Semantics.clause_sound_for_model].
    (* Name the renamed atom's components for convenience *)
    pose proof (Hren_db a Hin_a) as Hin_db.
    (* RA := Build_atom (atom_fn a) (map ld (atom_args a)) (ld (atom_ret a)) *)
    set (RA := Build_atom (atom_fn a)
                 (map (named_list_lookup default sub1) (atom_args a))
                 (named_list_lookup default sub1 (atom_ret a))) in Hin_db.
    (* RA is in db_to_atoms (db e_assum) *)
    pose proof (proj2 (in_db_to_atoms_iff_atom_in_db RA (db e_assum)) Hin_db) as Hin_list.
    (* atom_clause RA is in map atom_clause (db_to_atoms ...) *)
    pose proof (in_map (@atom_clause idx symbol) _ _ Hin_list) as Hin_clause.
    (* Extract soundness of RA from Hass *)
    pose proof (in_all (Semantics.clause_sound_for_model idx symbol idx_map m a_opt)
                  _ _ Hass Hin_clause) as Hsnd_RA.
    cbn [Semantics.clause_sound_for_model] in Hsnd_RA.
    (* Now unfold atom_sound_for_model for RA and expand RA's fields *)
    unfold Semantics.atom_sound_for_model in Hsnd_RA.
    unfold RA in Hsnd_RA.
    cbn [atom_fn atom_args atom_ret] in Hsnd_RA.
    (* Destruct the list_Mmap *)
    destruct (list_Mmap (map.get a_opt)
                (map (named_list_lookup default sub1) (atom_args a)))
      as [doms|] eqn:Hdoms.
    2:{ cbn [Is_Some_satisfying] in Hsnd_RA. contradiction. }
    cbn [Is_Some_satisfying] in Hsnd_RA.
    (* Destruct the map.get for ret *)
    destruct (map.get a_opt (named_list_lookup default sub1 (atom_ret a)))
      as [out_d|] eqn:Hout.
    2:{ cbn [Is_Some_satisfying] in Hsnd_RA. contradiction. }
    cbn [Is_Some_satisfying] in Hsnd_RA.
    (* Now build the goal for pullback_assignment *)
    unfold Semantics.atom_sound_for_model.
    (* Get the sub1 image for atom_ret a *)
    destruct (Hvars a Hin_a (atom_ret a) (or_introl eq_refl)) as [y_ret Hy_ret].
    pose proof (named_list_lookup_err_to_lookup default sub1 (atom_ret a) y_ret Hy_ret)
      as Hld_ret.
    rewrite Hld_ret in Hout.
    (* list_Mmap with pullback on args *)
    assert (Hargs_vars : forall x, In x (atom_args a) ->
              exists y, named_list_lookup_err sub1 x = Some y).
    { intros x Hx. exact (Hvars a Hin_a x (or_intror Hx)). }
    pose proof (list_Mmap_pullback_some a_opt sub1 (atom_args a) doms
                  Hargs_vars Hdoms) as Hmap_pb.
    rewrite Hmap_pb. cbn [Is_Some_satisfying].
    (* map.get pullback on ret *)
    rewrite (get_pullback_assignment_some a_opt sub1 (atom_ret a) y_ret out_d
               Hy_ret Hout).
    cbn [Is_Some_satisfying].
    exact Hsnd_RA.
  Qed.

  Definition good_sequent (s : sequent) : Prop :=
    clauses_good [] (s.(seq_assumptions) ++ s.(seq_conclusions)).

  (* ============================================================== *)
  (* Helper: building a "read-back" sequent                           *)
  (* ============================================================== *)

  (* A sequent built from a list of assumption atoms (with no eqs),
     a list of conclusion eqs, and a list of conclusion atoms.  This
     mirrors the exact shape that QueryOpt.sequent_of_states produces. *)
  Definition mk_seq (atoms_assum : list atom) (eqs : list (idx * idx))
             (atoms_concl : list atom) : sequent :=
    Build_sequent _ _
      (map atom_clause atoms_assum)
      (map (uncurry eq_clause) eqs ++ map atom_clause atoms_concl).

  (* The predicate live_eqn used by QueryOpt for the dead-equation
     filter (QueryOpt.v:394-401). *)
  Definition in_atoms (atoms : list atom) (x : idx) : bool :=
    existsb (fun a => orb (eqb a.(atom_ret) x) (inb x a.(atom_args))) atoms.

  Definition live_eqn (atoms : list atom) (p : idx * idx) : bool :=
    let '(x, y) := p in
    andb (andb (negb (eqb x y)) (in_atoms atoms x)) (in_atoms atoms y).

  (* ============================================================== *)
  (* Arrow G (forward): filtering dead equations is a subset, which  *)
  (* is sound by clause-monotonicity.                                 *)
  (* ============================================================== *)

  Lemma filter_live_eqn_forward
        (atoms_assum atoms_concl : list atom) (eqs : list (idx * idx))
        (m : model symbol) :
    let atoms := atoms_assum ++ atoms_concl in
    model_satisfies_rule m (mk_seq atoms_assum eqs atoms_concl) ->
    model_satisfies_rule m
      (mk_seq atoms_assum (filter (live_eqn atoms) eqs) atoms_concl).
  Proof.
    intros atoms Hfull a Hkeys Hass.
    (* Same forall_vars and same assumptions: just apply the hyp. *)
    specialize (Hfull a Hkeys Hass).
    destruct Hfull as [a' [Hext Hconc] ].
    exists a'; split; auto.
    (* The conclusion of [mk_seq atoms_assum (filter ...) atoms_concl] is a
       subset of [mk_seq atoms_assum eqs atoms_concl]. *)
    cbn [mk_seq seq_conclusions] in *.
    apply all_app; apply all_app in Hconc.
    destruct Hconc as [Heqs Hatoms]; split; trivial.
    (* The filtered eqs are a sublist of the original eqs. *)
    clear - Heqs.
    induction eqs as [|p eqs IH]; cbn in *; trivial.
    destruct (live_eqn atoms p); cbn in *.
    - destruct Heqs as [Hp Heqs]; split; auto.
    - destruct Heqs as [_ Heqs]; auto.
  Qed.

  (* ============================================================== *)
  (* Main theorem                                                     *)
  (* ============================================================== *)

  (* The intended statement: every model satisfies the optimised
     sequent iff it satisfies the original.

     The proof strategy (see /root/.claude/plans/queryopt-v-is-a-file-
     hidden-nest.md) is to decompose [optimize_sequent] into seven
     pipeline arrows (A: clauses_to_instance; B/D: rebuild; C: continue
     clauses_to_instance; E: force_equiv; F: db_remove of assumption
     atoms; G: filter dead equations) and prove that each preserves
     [sequent_equiv] of the read-back sequent.  The deepest piece is
     [clauses_to_instance_sound], which establishes a bridge between
     the [named_list] renaming produced by [clauses_to_instance] and a
     model assignment over the e-graph ids.

     The reusable infrastructure above ([clause_sound_extend],
     [all_clause_sound_extend], [in_db_to_atoms_iff_atom_in_db], the PER
     instances for [sequent_equiv]) gives the foundation; the per-arrow
     lemmas remain to be proved. *)
  (* ============================================================== *)
  (* Forward + reverse directions of the main theorem                 *)
  (* ============================================================== *)

  (* Forward: any model satisfying [s] also satisfies [optimize_sequent s].
     Intuition: the optimiser only weakens the sequent (dedups, drops
     dead eqs), so any satisfying assignment for [s] extends to one
     for the optimised form via the renaming built by
     [clauses_to_instance]. *)
  (* Helper: optimize_sequent on the empty sequent reduces to a sequent
     with no assumptions and only trivial conclusions, which any model
     satisfies. *)
  Lemma optimize_sequent_empty_satisfies (m : model symbol) :
    model_satisfies_rule m
      (optimize_sequent {| seq_assumptions := []; seq_conclusions := [] |}).
  Proof.
    intros a_opt Hkeys Hass; cbn -[map.tuples Properties.map.fold_empty] in *.
    replace (db_to_atoms map.empty : list atom) with (@nil atom)
      by (symmetry; apply db_to_atoms_empty).
    cbn [list_Miter]. unfold Mret in *.
    cbn -[db_to_atoms map.tuples] in *.
    replace (map.tuples
               (parent
                  (snd
                     (force_uf idx Eqb_idx idx_map
                        (empty (WithDefault idx) (idx_map idx)
                           (idx_map nat) idx_zero))))) with (@nil (idx*idx)).
    { exists a_opt. split; [intros ? ? Hk; exact Hk|]. cbn. trivial. }
    { cbn. unfold map.tuples. cbn -[map.fold map.keys].
      unfold UnionFind.empty. cbn -[map.fold map.keys].
      unfold force_uf. cbn [parent].
      unfold map.keys, map.tuples.
      rewrite !Properties.map.fold_empty. cbn.
      rewrite Properties.map.fold_empty. reflexivity. }
  Qed.

  Lemma optimize_sequent_forward (s : sequent) (m : model symbol) :
    good_sequent s ->
    model_satisfies_rule m s ->
    model_satisfies_rule m (optimize_sequent s).
  Proof.
    destruct s as [ [|c_a cs_a] [|c_c cs_c] ]; intros Hgood Hsat.
    - apply optimize_sequent_empty_satisfies.
    - admit.
    - admit.
    - admit.
  Admitted.

  (* Reverse: any model satisfying [optimize_sequent s] also satisfies [s].
     Intuition: the dedup'd conclusion atoms are entailed by the
     assumptions; the dropped reflexive eqs are witnessed by atom
     soundness (which gives [domain_wf]); the dropped dangling eqs are
     ruled out by [good_sequent]. *)
  Lemma optimize_sequent_reverse (s : sequent) (m : model symbol) :
    good_sequent s ->
    model_satisfies_rule m (optimize_sequent s) ->
    model_satisfies_rule m s.
  Proof.
    destruct s as [ [|c_a cs_a] [|c_c cs_c] ]; intros Hgood Hopt.
    - (* Empty-empty: model_satisfies_rule m (empty sequent) is trivial. *)
      intros a Hkeys Hass. exists a; split; [intros ? ? Hk; exact Hk | cbn; trivial].
    - admit.
    - admit.
    - admit.
  Admitted.

  Theorem optimize_sequent_equiv (s : sequent) :
    good_sequent s ->
    sequent_equiv (optimize_sequent s) s.
  Proof.
    intros Hgood m; split.
    - apply optimize_sequent_reverse; assumption.
    - apply optimize_sequent_forward; assumption.
  Qed.

End WithMap.
