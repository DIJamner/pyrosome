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
