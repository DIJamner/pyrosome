From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List Classes.RelationClasses.
Import ListNotations.
Open Scope list.

From Stdlib Require Import Logic.PropExtensionality
  Logic.FunctionalExtensionality.

From coqutil Require Import Map.Interface.

From Utils Require Import Utils UnionFind Monad ExtraMaps Relations Maps VC.
From Utils.EGraph Require Import Defs Semantics QueryOpt SemanticsAreUnified SemanticsUtil
  SemanticsSaturate SemanticsExecConst.
Import Monad.StateMonad.

(*
  This file states and proves that QueryOpt.optimize_sequent preserves
  the model-theoretic semantics of a sequent under the [good_sequent]
  precondition (which excludes the orphan-eqs edge case where the
  optimiser would be unsound).

  Status:

  - ON THE egraph_sound PATH: [optimize_sequent_forward_atoms]
    (atom-only, hash-consed assumptions as produced by
    [rule_to_log_rule]).  This lemma is FULLY PROVED, 0 axioms
    ("Closed under the global context"), and is the form consumed by
    Phase 6 / schedule_sound.  It is what downstream soundness needs.

  - OFF the egraph_sound PATH (general bidirectional equivalence, a
    SEPARATE and still-incomplete deliverable -- NOT the goal):
    [optimize_sequent_equiv], composed from [optimize_sequent_forward]
    and [optimize_sequent_reverse].  Each direction proves only the
    empty-empty branch and `admit`s the three non-empty branches.
    Verified via [Print Assumptions egraph_sound]: these three lemmas
    do NOT appear among egraph_sound's assumptions.  Do not mistake
    them for remaining work on egraph_sound (see the quarantine banner
    above [optimize_sequent_forward] below).  The general theorem would
    need L11 [clauses_to_instance_sound], the renaming<->assignment
    bridge between source variables and canonical e-graph ids.
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
       on the optimised side after canonicalisation renames keys.
       A ⊆-confinement premise is also added: every key of [a] must be in
       [forall_vars r], ensuring the domain of the assignment is exactly the
       variable set of the sequent. *)
    Definition model_satisfies_rule (r : sequent) : Prop :=
      forall a : idx_map domain,
        (forall x, In x (forall_vars r) -> Sep.has_key x a) ->
        (forall x, Sep.has_key x a -> In x (forall_vars r)) ->
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
                     Sep.has_key z (parent (equiv e'))) /\
          (forall y d, map.get i' y = Some d ->
                       map.get i y = Some d \/
                       (exists x', named_list_lookup_err sub' x' = Some y))
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
      split; [intros z Hz; exact Hz|].
      intros y d Hyd; left; exact Hyd. }
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
    split; [exact Hk_pres|].
    intros y d Hyd.
    pose proof (Eqb_idx_ok y x_new) as Hyxn_dec.
    destruct (eqb y x_new) eqn:Hyxn.
    - right. assert (Heqy : y = x_new) by exact Hyxn_dec. subst y.
      exists x. cbn [named_list_lookup_err].
      assert (Hxx : eqb x x = true) by
        (pose proof (Eqb_idx_ok x x) as Hxx_dec;
         destruct (eqb x x); [reflexivity | exfalso; apply Hxx_dec; reflexivity]).
      rewrite Hxx. reflexivity.
    - left. rewrite map.get_put_diff in Hyd; [exact Hyd | exact Hyxn_dec].
  Qed.

  (* ============================================================== *)
  (* sub_mono helpers (early copy): needed by list_Mmap_rename_lookup_sound *)
  (* ============================================================== *)

  Local Lemma rename_lookup_sub_mono_early (x : idx) (sub0 : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit)
    (z w : idx) :
    named_list_lookup_err sub0 z = Some w ->
    named_list_lookup_err
      (snd (fst (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                   unit x sub0 e0))) z = Some w.
  Proof.
    intros Hhit.
    unfold rename_lookup.
    destruct (named_list_lookup_err sub0 x) as [y|] eqn:Hlook.
    - cbn [Mret StateMonad.state_monad fst snd]. exact Hhit.
    - cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
      cbn beta iota. unfold Basics.compose.
      destruct (alloc idx idx_succ symbol symbol_map idx_map idx_trie unit e0)
        as [fresh e1] eqn:Halloc.
      cbn [fst snd].
      cbn [named_list_lookup_err].
      assert (Hzx : z <> x).
      { intros Heq. subst z. rewrite Hlook in Hhit. discriminate. }
      pose proof (Eqb_idx_ok z x) as Hdec.
      destruct (eqb z x) eqn:Hzxeqb.
      + exfalso. apply Hzx. exact Hdec.
      + exact Hhit.
  Qed.

  Local Lemma list_Mmap_rename_lookup_sub_mono_early (args : list idx) :
    forall (sub0 : named_list idx idx)
      (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit)
      (z w : idx),
    named_list_lookup_err sub0 z = Some w ->
    named_list_lookup_err
      (snd (fst (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                              idx_trie unit) args sub0 e0))) z = Some w.
  Proof.
    induction args as [|a args IH]; intros sub0 e0 z w Hhit.
    - cbn. exact Hhit.
    - cbn [list_Mmap].
      destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                  unit a sub0 e0) as [p e1] eqn:Hrla.
      destruct p as [a' sub1].
      destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                             idx_trie unit) args sub1 e1) as [p2 e2] eqn:Hrec.
      destruct p2 as [args' sub2].
      pose proof (rename_lookup_sub_mono_early a sub0 e0 z w Hhit) as Hstep.
      rewrite Hrla in Hstep. cbn [fst snd] in Hstep.
      pose proof (IH sub1 e1 z w Hstep) as Hrec_mono.
      rewrite Hrec in Hrec_mono. cbn [fst snd] in Hrec_mono.
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
      cbn beta iota. unfold Basics.compose.
      rewrite Hrla. cbn [fst snd uncurry].
      destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                             idx_trie unit) args sub1 e1) as [q e3] eqn:Hq.
      destruct q as [args2 sub3]. cbn [fst snd uncurry].
      injection Hrec as <- <-.
      exact Hrec_mono.
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
                     Sep.has_key z (parent (equiv e'))) /\
          (forall y d, map.get i' y = Some d ->
                       map.get i y = Some d \/
                       (exists x', named_list_lookup_err sub' x' = Some y))
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
      split; [intros z Hz; exact Hz|].
      intros y d Hyd; left; exact Hyd.
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
                       Hka'1 & Hmono1 & Hdom1).
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
                       Hall2 & Hmono2 & Hdom2).
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
      split; [intros z Hz; apply Hmono2; apply Hmono1; exact Hz|].
      { intros y d Hyd.
        destruct (Hdom2 y d Hyd) as [Hi1 | Hsub2].
        - destruct (Hdom1 y d Hi1) as [Hi0 | Hsub1].
          + left; exact Hi0.
          + right. destruct Hsub1 as [x'' Hx''].
            exists x''.
            exact (eq_rect _ (fun p => named_list_lookup_err (snd (fst p)) x'' = Some y)
                     (list_Mmap_rename_lookup_sub_mono_early args0 sub1 e1 x'' y Hx'')
                     _ Hlm).
        - right; exact Hsub2. }
  Qed.

  (* ============================================================== *)
  (* sub_mono helpers: clauses_to_instance preserves sub entries    *)
  (* ============================================================== *)

  Local Lemma rename_lookup_sub_mono (x : idx) (sub0 : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit)
    (z w : idx) :
    named_list_lookup_err sub0 z = Some w ->
    named_list_lookup_err
      (snd (fst (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                   unit x sub0 e0))) z = Some w.
  Proof.
    intros Hhit.
    unfold rename_lookup.
    destruct (named_list_lookup_err sub0 x) as [y|] eqn:Hlook.
    - (* hit: sub unchanged *)
      cbn [Mret StateMonad.state_monad fst snd]. exact Hhit.
    - (* miss: prepend (x, fresh) *)
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
      cbn beta iota. unfold Basics.compose.
      destruct (alloc idx idx_succ symbol symbol_map idx_map idx_trie unit e0)
        as [fresh e1] eqn:Halloc.
      cbn [fst snd].
      (* named_list_lookup_err ((x, fresh) :: sub0) z *)
      cbn [named_list_lookup_err].
      assert (Hzx : z <> x).
      { intros Heq. subst z. rewrite Hlook in Hhit. discriminate. }
      pose proof (Eqb_idx_ok z x) as Hdec.
      destruct (eqb z x) eqn:Hzxeqb.
      + exfalso. apply Hzx. exact Hdec.
      + exact Hhit.
  Qed.

  Local Lemma list_Mmap_rename_lookup_sub_mono (args : list idx) :
    forall (sub0 : named_list idx idx)
      (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit)
      (z w : idx),
    named_list_lookup_err sub0 z = Some w ->
    named_list_lookup_err
      (snd (fst (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                              idx_trie unit) args sub0 e0))) z = Some w.
  Proof.
    induction args as [|a args IH]; intros sub0 e0 z w Hhit.
    - cbn. exact Hhit.
    - cbn [list_Mmap].
      destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                  unit a sub0 e0) as [p e1] eqn:Hrla.
      destruct p as [a' sub1].
      destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                             idx_trie unit) args sub1 e1) as [p2 e2] eqn:Hrec.
      destruct p2 as [args' sub2].
      (* Compute the sub monotonicity along each step *)
      pose proof (rename_lookup_sub_mono a sub0 e0 z w Hhit) as Hstep.
      rewrite Hrla in Hstep. cbn [fst snd] in Hstep.
      pose proof (IH sub1 e1 z w Hstep) as Hrec_mono.
      rewrite Hrec in Hrec_mono. cbn [fst snd] in Hrec_mono.
      (* Now reduce the goal *)
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
      cbn beta iota. unfold Basics.compose.
      rewrite Hrla. cbn [fst snd uncurry].
      destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                             idx_trie unit) args sub1 e1) as [q e3] eqn:Hq.
      destruct q as [args2 sub3]. cbn [fst snd uncurry].
      injection Hrec as <- <-.
      exact Hrec_mono.
  Qed.

  Local Lemma rename_atom_sub_mono (a : atom) (sub0 : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit)
    (z w : idx) :
    named_list_lookup_err sub0 z = Some w ->
    named_list_lookup_err
      (snd (fst (rename_atom idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                   unit a sub0 e0))) z = Some w.
  Proof.
    intros Hhit.
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
    cbn [fst snd uncurry].
    (* Goal should now be: named_list_lookup_err sub2 z = Some w *)
    pose proof (list_Mmap_rename_lookup_sub_mono args sub0 e0 z w Hhit) as Hstep1.
    set (LM := list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                            idx_trie unit) args sub0 e0) in *.
    rewrite Hq1 in Hstep1. cbn [fst snd] in Hstep1.
    pose proof (rename_lookup_sub_mono out sub1 e1 z w Hstep1) as Hstep2.
    set (RL := rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit
                 out sub1 e1) in *.
    rewrite Hq2 in Hstep2. cbn [fst snd] in Hstep2.
    exact Hstep2.
  Qed.

  Local Lemma add_clause_to_instance_sub_mono
    (c : Semantics.clause idx symbol)
    (sub0 : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit)
    (z w : idx) :
    named_list_lookup_err sub0 z = Some w ->
    named_list_lookup_err
      (snd (fst (add_clause_to_instance idx Eqb_idx idx_succ symbol symbol_map idx_map
                   idx_trie unit c sub0 e0))) z = Some w.
  Proof.
    intros Hhit.
    destruct c as [x y | a_clause].
    - (* eq_clause x y *)
      unfold add_clause_to_instance.
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
      cbn beta iota. unfold Basics.compose.
      destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                  unit x sub0 e0) as [p1 e1'] eqn:Hrx.
      destruct p1 as [x' sub1'].
      cbn [fst snd uncurry].
      destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                  unit y sub1' e1') as [p2 e2'] eqn:Hry.
      destruct p2 as [y' sub2'].
      cbn [fst snd uncurry].
      cbn [lift StateMonad.state_monad Mbind Mret fst snd].
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mseq Mbind Mret].
      cbn beta iota. unfold Basics.compose.
      destruct (Defs.union x' y' e2') as [v e3'] eqn:Hu.
      cbn [uncurry fst snd].
      (* sub2' is the final sub; union doesn't touch it *)
      pose proof (rename_lookup_sub_mono x sub0 e0 z w Hhit) as Hstep1.
      rewrite Hrx in Hstep1. cbn [fst snd] in Hstep1.
      pose proof (rename_lookup_sub_mono y sub1' e1' z w Hstep1) as Hstep2.
      rewrite Hry in Hstep2. cbn [fst snd] in Hstep2.
      exact Hstep2.
    - (* atom_clause a_clause *)
      unfold add_clause_to_instance.
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
      cbn beta iota. unfold Basics.compose.
      destruct (rename_atom idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                  unit a_clause sub0 e0) as [p1 e1'] eqn:Hra.
      destruct p1 as [a' sub1'].
      cbn [fst snd uncurry].
      cbn [lift StateMonad.state_monad Mbind Mret fst snd].
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mseq Mbind Mret].
      cbn beta iota. unfold Basics.compose.
      destruct (update_entry a' e1') as [u' e2'] eqn:Hue.
      cbn [uncurry fst snd].
      (* sub1' is the final sub; update_entry doesn't touch it *)
      pose proof (rename_atom_sub_mono a_clause sub0 e0 z w Hhit) as Hstep.
      rewrite Hra in Hstep. cbn [fst snd] in Hstep.
      exact Hstep.
  Qed.

  Lemma clauses_to_instance_sub_mono
    (cs : list (Semantics.clause idx symbol))
    (sub0 : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit)
    (z w : idx) :
    named_list_lookup_err sub0 z = Some w ->
    match clauses_to_instance idx_succ (analysis_result:=unit) cs sub0 e0 with
    | (_, sub1, _) => named_list_lookup_err sub1 z = Some w
    end.
  Proof.
    revert sub0 e0.
    induction cs as [|c cs IH]; intros sub0 e0 Hhit.
    - cbn. exact Hhit.
    - cbn [Semantics.clauses_to_instance list_Miter].
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mseq Mbind Mret].
      cbn beta iota. unfold Basics.compose.
      destruct (add_clause_to_instance idx Eqb_idx idx_succ symbol symbol_map
                  idx_map idx_trie unit c sub0 e0) as [q e1] eqn:Hadd.
      destruct q as [u sub1].
      cbn [snd uncurry].
      apply IH.
      pose proof (add_clause_to_instance_sub_mono c sub0 e0 z w Hhit) as Hstep.
      rewrite Hadd in Hstep. cbn [fst snd] in Hstep.
      exact Hstep.
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
    | ((_, sub_final), e1) =>
        Semantics.egraph_ok idx lt symbol symbol_map idx_map idx_trie unit e1 /\
        exists i',
          map.extends i' i /\
          Semantics.egraph_sound_for_interpretation
            idx symbol symbol_map idx_map idx_trie unit m i' e1 /\
          (forall x y, In (x, y) sub_final ->
                 forall d, map.get a_src x = Some d -> map.get i' y = Some d) /\
          (forall y d, map.get i' y = Some d ->
                       map.get i y = Some d \/
                       (exists x', named_list_lookup_err sub_final x' = Some y))
    end.
  Proof.
    revert sub0 e0 i.
    induction cs as [|c cs IH]; intros sub0 e0 i Hok Hsnd Hren Hsubdom Hcs.
    - cbn. split; [exact Hok|]. exists i.
      split; [intros ? ? Hk; exact Hk|].
      split; [exact Hsnd|].
      split; [exact Hren|].
      intros y d Hyd; left; exact Hyd.
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
          assert (Hpost_IH : let '((_, sub_f), e1) := clauses_to_instance idx_succ cs
                                              ((y, y_new) :: sub0) e_unioned in
                             egraph_ok idx lt symbol symbol_map idx_map idx_trie
                               unit e1 /\
                             (exists i' : idx_map (domain symbol m),
                                map.extends i' (map.put i y_new dy) /\
                                egraph_sound_for_interpretation idx symbol
                                  symbol_map idx_map idx_trie unit m i' e1 /\
                                (forall a b, In (a, b) sub_f ->
                                   forall d, map.get a_src a = Some d -> map.get i' b = Some d) /\
                                (forall z0 d0, map.get i' z0 = Some d0 ->
                                   map.get (map.put i y_new dy) z0 = Some d0 \/
                                   (exists x'', named_list_lookup_err sub_f x'' = Some z0)))).
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
            as [ [u_pp sub_final] e_final ] eqn:Hci.
          destruct Hpost_IH as (Hok_f & i_final & Hext_f & Hsnd_f & Hren_f & Hdom_f).
          split; [exact Hok_f|].
          exists i_final.
          refine (conj _ (conj Hsnd_f (conj Hren_f _))).
          { intros k d Hk.
            apply Hext_f.
            rewrite map.get_put_diff; [exact Hk|].
            intros Heq. subst k. rewrite Hi_ynew_none in Hk. discriminate. }
          { intros y0 d Hyd.
            destruct (Hdom_f y0 d Hyd) as [Hput | Hsub].
            { pose proof (Eqb_idx_ok y0 y_new) as Hy0yn_dec.
              destruct (eqb y0 y_new) eqn:Hy0yn.
              { right. assert (Heqy0 : y0 = y_new) by exact Hy0yn_dec. subst y0.
                exists y.
                pose proof (clauses_to_instance_sub_mono cs ((y, y_new) :: sub0) e_unioned y y_new) as Hsm.
                cbn [named_list_lookup_err] in Hsm.
                assert (Hyy : eqb y y = true) by
                  (pose proof (Eqb_idx_ok y y) as Hd;
                   destruct (eqb y y); [reflexivity | exfalso; apply Hd; reflexivity]).
                rewrite Hyy in Hsm. specialize (Hsm eq_refl).
                rewrite Hci in Hsm. cbn [fst snd] in Hsm. exact Hsm. }
              { left. rewrite map.get_put_diff in Hput; [exact Hput | exact Hy0yn_dec]. } }
            { right; exact Hsub. } }
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
          assert (Hpost_IH : let '((_, sub_f), e1) := clauses_to_instance idx_succ cs
                                              ((x, x_new) :: sub0) e_unioned in
                             egraph_ok idx lt symbol symbol_map idx_map idx_trie
                               unit e1 /\
                             (exists i' : idx_map (domain symbol m),
                                map.extends i' (map.put i x_new dx) /\
                                egraph_sound_for_interpretation idx symbol
                                  symbol_map idx_map idx_trie unit m i' e1 /\
                                (forall a b, In (a, b) sub_f ->
                                   forall d, map.get a_src a = Some d -> map.get i' b = Some d) /\
                                (forall z0 d0, map.get i' z0 = Some d0 ->
                                   map.get (map.put i x_new dx) z0 = Some d0 \/
                                   (exists x'', named_list_lookup_err sub_f x'' = Some z0)))).
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
            as [ [u_pp sub_final] e_final ] eqn:Hci.
          destruct Hpost_IH as (Hok_f & i_final & Hext_f & Hsnd_f & Hren_f & Hdom_f).
          split; [exact Hok_f|].
          exists i_final.
          refine (conj _ (conj Hsnd_f (conj Hren_f _))).
          { intros k d Hk.
            apply Hext_f.
            rewrite map.get_put_diff; [exact Hk|].
            intros Heq. subst k. rewrite Hi_xnew_none in Hk. discriminate. }
          { intros y0 d Hyd.
            destruct (Hdom_f y0 d Hyd) as [Hput | Hsub].
            { pose proof (Eqb_idx_ok y0 x_new) as Hy0xn_dec.
              destruct (eqb y0 x_new) eqn:Hy0xn.
              { right. assert (Heqy0 : y0 = x_new) by exact Hy0xn_dec. subst y0.
                exists x.
                pose proof (clauses_to_instance_sub_mono cs ((x, x_new) :: sub0) e_unioned x x_new) as Hsm.
                cbn [named_list_lookup_err] in Hsm.
                assert (Hxx : eqb x x = true) by
                  (pose proof (Eqb_idx_ok x x) as Hd;
                   destruct (eqb x x); [reflexivity | exfalso; apply Hd; reflexivity]).
                rewrite Hxx in Hsm. specialize (Hsm eq_refl).
                rewrite Hci in Hsm. cbn [fst snd] in Hsm. exact Hsm. }
              { left. rewrite map.get_put_diff in Hput; [exact Hput | exact Hy0xn_dec]. } }
            { right; exact Hsub. } }
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
            assert (Hpost_IH : let '((_, sub_f), e1) := clauses_to_instance idx_succ cs
                                                ((x, x_new) :: sub0) e_unioned in
                               egraph_ok idx lt symbol symbol_map idx_map idx_trie
                                 unit e1 /\
                               (exists i' : idx_map (domain symbol m),
                                  map.extends i' (map.put i x_new dx) /\
                                  egraph_sound_for_interpretation idx symbol
                                    symbol_map idx_map idx_trie unit m i' e1 /\
                                  (forall a b, In (a, b) sub_f ->
                                     forall d, map.get a_src a = Some d -> map.get i' b = Some d) /\
                                  (forall z0 d0, map.get i' z0 = Some d0 ->
                                     map.get (map.put i x_new dx) z0 = Some d0 \/
                                     (exists x'', named_list_lookup_err sub_f x'' = Some z0)))).
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
              as [ [u_pp sub_final] e_final ] eqn:Hci.
            destruct Hpost_IH as (Hok_f & i_final & Hext_f & Hsnd_f & Hren_f & Hdom_f).
            split; [exact Hok_f|].
            exists i_final.
            refine (conj _ (conj Hsnd_f (conj Hren_f _))).
            { intros k d Hk.
              apply Hext_f.
              rewrite map.get_put_diff; [exact Hk|].
              intros Heq. subst k. rewrite Hi_xnew_none in Hk. discriminate. }
            { intros y0 d Hyd.
              destruct (Hdom_f y0 d Hyd) as [Hput | Hsub].
              { pose proof (Eqb_idx_ok y0 x_new) as Hy0xn_dec.
                destruct (eqb y0 x_new) eqn:Hy0xn.
                { right. assert (Heqy0 : y0 = x_new) by exact Hy0xn_dec. subst y0.
                  exists x.
                  pose proof (clauses_to_instance_sub_mono cs ((x, x_new) :: sub0) e_unioned x x_new) as Hsm.
                  cbn [named_list_lookup_err] in Hsm.
                  assert (Hxx2 : eqb x x = true) by
                    (pose proof (Eqb_idx_ok x x) as Hd;
                     destruct (eqb x x); [reflexivity | exfalso; apply Hd; reflexivity]).
                  rewrite Hxx2 in Hsm. specialize (Hsm eq_refl).
                  rewrite Hci in Hsm. cbn [fst snd] in Hsm. exact Hsm. }
                { left. rewrite map.get_put_diff in Hput; [exact Hput | exact Hy0xn_dec]. } }
              { right; exact Hsub. } } }
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
          assert (Hpost_IH : let '((_, sub_f), e1) := clauses_to_instance idx_succ cs
                                              ((y, y_new) :: (x, x_new) :: sub0) e_unioned in
                             egraph_ok idx lt symbol symbol_map idx_map idx_trie
                               unit e1 /\
                             (exists i' : idx_map (domain symbol m),
                                map.extends i' (map.put (map.put i x_new dx) y_new dy) /\
                                egraph_sound_for_interpretation idx symbol
                                  symbol_map idx_map idx_trie unit m i' e1 /\
                                (forall a b, In (a, b) sub_f ->
                                   forall d, map.get a_src a = Some d -> map.get i' b = Some d) /\
                                (forall z0 d0, map.get i' z0 = Some d0 ->
                                   map.get (map.put (map.put i x_new dx) y_new dy) z0 = Some d0 \/
                                   (exists x'', named_list_lookup_err sub_f x'' = Some z0)))).
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
            as [ [u_pp sub_final] e_final ] eqn:Hci.
          destruct Hpost_IH as (Hok_f & i_final & Hext_f & Hsnd_f & Hren_f & Hdom_f).
          split; [exact Hok_f|].
          exists i_final.
          assert (Hyx_idx_neq : y_new <> x_new) by (intros Heq; apply Hxy_idx_neq; symmetry; exact Heq).
          assert (Hi_ynew_orig : map.get i y_new = None).
          { rewrite map.get_put_diff in Hi_ynew_none.
            - exact Hi_ynew_none.
            - exact Hyx_idx_neq. }
          refine (conj _ (conj Hsnd_f (conj Hren_f _))).
          { intros k d Hk.
            apply Hext_f.
            rewrite map.get_put_diff.
            2: { intros Heq. subst k. rewrite Hi_ynew_orig in Hk. discriminate. }
            rewrite map.get_put_diff; [exact Hk|].
            intros Heq. subst k. rewrite Hi_xnew_none in Hk. discriminate. }
          { intros y0 d Hyd.
            destruct (Hdom_f y0 d Hyd) as [Hput | Hsub].
            { pose proof (Eqb_idx_ok y0 y_new) as Hy0yn_dec.
              destruct (eqb y0 y_new) eqn:Hy0yn.
              { right. assert (Heqy0 : y0 = y_new) by exact Hy0yn_dec. subst y0.
                exists y.
                pose proof (clauses_to_instance_sub_mono cs ((y, y_new) :: (x, x_new) :: sub0) e_unioned y y_new) as Hsm.
                cbn [named_list_lookup_err] in Hsm.
                assert (Hyy2 : eqb y y = true) by
                  (pose proof (Eqb_idx_ok y y) as Hd;
                   destruct (eqb y y); [reflexivity | exfalso; apply Hd; reflexivity]).
                rewrite Hyy2 in Hsm. specialize (Hsm eq_refl).
                rewrite Hci in Hsm. cbn [fst snd] in Hsm. exact Hsm. }
              { rewrite map.get_put_diff in Hput by exact Hy0yn_dec.
                pose proof (Eqb_idx_ok y0 x_new) as Hy0xn_dec.
                destruct (eqb y0 x_new) eqn:Hy0xn.
                { right. assert (Heqy0 : y0 = x_new) by exact Hy0xn_dec. subst y0.
                  exists x.
                  pose proof (clauses_to_instance_sub_mono cs ((y, y_new) :: (x, x_new) :: sub0) e_unioned x x_new) as Hsm.
                  cbn [named_list_lookup_err] in Hsm.
                  assert (Hyx2 : eqb x y = false) by
                    (pose proof (Eqb_idx_ok x y) as Hd;
                     destruct (eqb x y) eqn:E; [exfalso; apply Hxy_neq; exact Hd | reflexivity]).
                  rewrite Hyx2 in Hsm.
                  assert (Hxx2 : eqb x x = true) by
                    (pose proof (Eqb_idx_ok x x) as Hd;
                     destruct (eqb x x); [reflexivity | exfalso; apply Hd; reflexivity]).
                  rewrite Hxx2 in Hsm. specialize (Hsm eq_refl).
                  rewrite Hci in Hsm. cbn [fst snd] in Hsm. exact Hsm. }
                { left. rewrite map.get_put_diff in Hput; [exact Hput | exact Hy0xn_dec]. } } }
            { right; exact Hsub. } }
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
                              Hall_args'1 & Hmono1 & Hdom_lm).
        cbn [uncurry Basics.compose].
        pose proof (rename_lookup_sound Hlti Hlts Hltt m Hm a_src out out_dom sub1 e1 i1
                      Hok1 Hsnd1 Hren1 Hsubdom1 Hout_src Hwf_out) as Hrl_out.
        destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                    unit out sub1 e1) as [ [out' sub2] e2 ] eqn:Hrlo.
        destruct Hrl_out as (i2 & Hext2 & Hok2 & Hsnd2 & Hren2 & Hsubdom2 & Hi2out' &
                             Hkout'2 & Hmono2 & Hdom_rl).
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
        destruct (clauses_to_instance idx_succ cs sub2 e3) as [ [u_pp sub_final] e_final ] eqn:Hci.
        destruct HIH as (Hok_f & i_final & Hext_f & Hsnd_f & Hren_f & Hdom_f).
        split; [exact Hok_f|].
        exists i_final.
        refine (conj _ (conj Hsnd_f (conj Hren_f _))).
        { intros k v Hk. apply Hext_f. apply Hext2. apply Hext1. exact Hk. }
        { intros y0 d Hyd.
          destruct (Hdom_f y0 d Hyd) as [Hi2 | Hsub_f].
          { destruct (Hdom_rl y0 d Hi2) as [Hi1 | Hsub2].
            { destruct (Hdom_lm y0 d Hi1) as [Hi0 | Hsub1].
              { left; exact Hi0. }
              { right. destruct Hsub1 as [x'' Hx''].
                exists x''.
                pose proof (eq_rect _
                  (fun p => named_list_lookup_err (snd (fst p)) x'' = Some y0)
                  (rename_lookup_sub_mono out sub1 e1 x'' y0 Hx'')
                  _ Hrlo) as Hs12.
                cbn [snd fst] in Hs12.
                pose proof (clauses_to_instance_sub_mono cs sub2 e3 x'' y0 Hs12) as Hs2f.
                rewrite Hci in Hs2f. exact Hs2f. } }
            { right. destruct Hsub2 as [x'' Hx''].
              exists x''.
              pose proof (clauses_to_instance_sub_mono cs sub2 e3 x'' y0 Hx'') as Hs2f.
              rewrite Hci in Hs2f. exact Hs2f. } }
          { right; exact Hsub_f. } }
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
  (* haskey_in helpers: reverse key-preservation                   *)
  (* ============================================================== *)

  (* find_aux only adds keys that already exist in pa (via map.put of existing key).
     So any key in the output was already in the input. *)
  Lemma find_aux_keys_in (mr : nat) :
    forall (i : idx) (pa : idx_map idx) z,
      Sep.has_key z (snd (find_aux idx Eqb_idx (idx_map idx) mr i pa)) ->
      Sep.has_key z pa.
  Proof.
    induction mr; intros i pa z Hz.
    - cbn in Hz. exact Hz.
    - cbn in Hz. destruct (map.get pa i) as [a|] eqn:Hpai; [|exact Hz].
      eqb_case a i; [exact Hz|].
      destruct (find_aux idx Eqb_idx (idx_map idx) mr a pa) as [v p'] eqn:Hfa.
      cbn in Hz.
      pose proof (IHmr a pa z) as IH. rewrite Hfa in IH. cbn in IH.
      unfold Sep.has_key in *.
      eqb_case z i.
      + rewrite Hpai. exact I.
      + rewrite map.get_put_diff in Hz by congruence. apply IH. exact Hz.
  Qed.

  Lemma UnionFind_find_keys_in
        (uf : union_find idx (idx_map idx) (idx_map nat)) (x : idx) :
    forall z,
      Sep.has_key z (fst (UnionFind.find uf x)).(parent) ->
      Sep.has_key z uf.(parent).
  Proof.
    intros z Hz. destruct uf as [ra pa mr nx]. cbn [parent] in Hz.
    unfold UnionFind.find in Hz.
    pose proof (find_aux_keys_in (S mr) x pa z) as Hk.
    destruct (find_aux idx Eqb_idx (idx_map idx) (S mr) x pa) as [cx f] eqn:Hfa.
    cbn [fst parent] in Hz. apply Hk. exact Hz.
  Qed.

  Lemma Defs_find_keys_in (x : idx) :
    forall e z,
      Sep.has_key z
        (parent (equiv (snd
          (@Defs.find idx Eqb_idx symbol symbol_map idx_map idx_trie unit x e)))) ->
      Sep.has_key z (parent (equiv e)).
  Proof.
    intros e z Hz. unfold Defs.find in Hz.
    destruct (UnionFind.find (equiv e) x) as [uf' v'] eqn:Hf. cbn in Hz.
    pose proof (UnionFind_find_keys_in (equiv e) x z) as Hk.
    rewrite Hf in Hk. cbn in Hk. apply Hk. exact Hz.
  Qed.

  (* find_aux return value is a key of the original map, when the map is value-closed *)
  Local Lemma find_aux_ret_haskey (mr : nat) :
    forall (i : idx) (pa : idx_map idx),
      Sep.has_key i pa ->
      (forall j k, map.get pa j = Some k -> Sep.has_key k pa) ->
      Sep.has_key (fst (find_aux idx Eqb_idx (idx_map idx) mr i pa)) pa.
  Proof.
    induction mr; intros i pa Hi Hclosed.
    - cbn. exact Hi.
    - cbn. destruct (map.get pa i) as [a|] eqn:Hpai.
      + eqb_case a i; [cbn; exact Hi|].
        destruct (find_aux idx Eqb_idx (idx_map idx) mr a pa) as [v f] eqn:Hfa.
        cbn [fst].
        pose proof (IHmr a pa (Hclosed i a Hpai) Hclosed) as IH2.
        rewrite Hfa in IH2. cbn [fst] in IH2. exact IH2.
      + cbn. exact Hi.
  Qed.

  (* UnionFind.find return is a key of the output parent map *)
  Local Lemma UnionFind_find_ret_haskey
        (uf : union_find idx (idx_map idx) (idx_map nat)) (x : idx) :
      Sep.has_key x (parent uf) ->
      (forall j k, map.get (parent uf) j = Some k -> Sep.has_key k (parent uf)) ->
      Sep.has_key (snd (UnionFind.find uf x))
                  (parent (fst (UnionFind.find uf x))).
  Proof.
    intros Hx Hclosed. destruct uf as [ra pa mr nx]. cbn [parent] in *.
    unfold UnionFind.find.
    destruct (find_aux idx Eqb_idx (idx_map idx) (S mr) x pa) as [cx f] eqn:Hfa.
    cbn [fst snd parent].
    pose proof (find_aux_ret_haskey (S mr) x pa Hx Hclosed) as Hcx.
    rewrite Hfa in Hcx. cbn [fst] in Hcx.
    pose proof (find_aux_keys_preserved (S mr) x pa cx Hcx) as Hfcx.
    rewrite Hfa in Hfcx. cbn [snd] in Hfcx. exact Hfcx.
  Qed.

  (* parent_closed: every value in the parent map is also a key *)
  Definition parent_closed (e : Defs.instance idx symbol symbol_map idx_map idx_trie unit) : Prop :=
    forall j k, map.get (parent (equiv e)) j = Some k ->
                Sep.has_key k (parent (equiv e)).

  Local Lemma alloc_maintains_parent_closed
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    parent_closed e0 ->
    parent_closed (snd (alloc idx idx_succ symbol symbol_map idx_map idx_trie unit e0)).
  Proof.
    intro Hc. unfold alloc.
    destruct (UnionFind.alloc idx (idx_map idx) (idx_map nat) idx_succ (equiv e0))
      as [eq' xf] eqn:Heq. cbn [snd].
    unfold UnionFind.alloc in Heq.
    destruct (equiv e0) as [ra pa mr nx] eqn:Heq0.
    cbn in Heq. injection Heq as <- <-.
    unfold parent_closed. cbn [parent equiv]. intros j k Hjk. unfold Sep.has_key.
    pose proof (Eqb_idx_ok j nx) as Hjnx_ok. destruct (eqb j nx) eqn:Hjnx.
    - subst j. rewrite map.get_put_same in Hjk. injection Hjk as <-.
      rewrite map.get_put_same. exact I.
    - rewrite map.get_put_diff in Hjk by exact Hjnx_ok.
      assert (Hk : Sep.has_key k (parent (equiv e0))).
      { apply (Hc j k). rewrite Heq0. cbn [parent]. exact Hjk. }
      rewrite Heq0 in Hk. cbn [parent] in Hk. unfold Sep.has_key in Hk.
      pose proof (Eqb_idx_ok k nx) as Hokk. destruct (eqb k nx) eqn:Hknx.
      + subst k. rewrite map.get_put_same. exact I.
      + rewrite map.get_put_diff by exact Hokk. exact Hk.
  Qed.

  Local Lemma find_aux_maintains_parent_closed (mr : nat) :
    forall (i : idx) (pa : idx_map idx),
      (forall j k, map.get pa j = Some k -> Sep.has_key k pa) ->
      forall j k, map.get (snd (find_aux idx Eqb_idx (idx_map idx) mr i pa)) j = Some k ->
                  Sep.has_key k (snd (find_aux idx Eqb_idx (idx_map idx) mr i pa)).
  Proof.
    induction mr; intros i pa Hclosed j k Hjk.
    - cbn in *. exact (Hclosed j k Hjk).
    - cbn [find_aux] in *.
      destruct (map.get pa i) as [a|] eqn:Hpai; [|exact (Hclosed j k Hjk)].
      eqb_case a i; [exact (Hclosed j k Hjk)|].
      destruct (find_aux idx Eqb_idx (idx_map idx) mr a pa) as [v f] eqn:Hfa.
      cbn [snd] in *.
      assert (Hclosed_f : forall j' k', map.get f j' = Some k' -> Sep.has_key k' f).
      { intros j' k' Hj'k'.
        pose proof (IHmr a pa Hclosed j' k') as IH.
        rewrite Hfa in IH. cbn [snd] in IH. exact (IH Hj'k'). }
      pose proof (find_aux_ret_haskey mr a pa (Hclosed i a Hpai) Hclosed) as Hv_pa.
      rewrite Hfa in Hv_pa. cbn [fst] in Hv_pa.
      pose proof (find_aux_keys_preserved mr a pa v Hv_pa) as Hv_f.
      rewrite Hfa in Hv_f. cbn [snd] in Hv_f.
      unfold Sep.has_key.
      pose proof (Eqb_idx_ok j i) as Hji_dec. destruct (eqb j i) eqn:Hji_eq.
      + subst j. rewrite map.get_put_same in Hjk. injection Hjk as <-.
        unfold Sep.has_key in Hv_f.
        pose proof (Eqb_idx_ok v i) as Hvi_dec. destruct (eqb v i) eqn:Hvi_eq.
        * subst v. rewrite map.get_put_same. exact I.
        * rewrite map.get_put_diff by exact Hvi_dec. exact Hv_f.
      + rewrite map.get_put_diff in Hjk by exact Hji_dec.
        pose proof (Hclosed_f j k Hjk) as Hk_f. unfold Sep.has_key in Hk_f.
        pose proof (Eqb_idx_ok k i) as Hki_dec. destruct (eqb k i) eqn:Hki_eq.
        * subst k. rewrite map.get_put_same. exact I.
        * rewrite map.get_put_diff by exact Hki_dec. exact Hk_f.
  Qed.

  Local Lemma Defs_find_maintains_parent_closed (x : idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    parent_closed e0 ->
    parent_closed (snd (@Defs.find idx Eqb_idx symbol symbol_map idx_map idx_trie unit x e0)).
  Proof.
    intro Hc. unfold parent_closed. unfold Defs.find.
    destruct (UnionFind.find (equiv e0) x) as [uf' v'] eqn:Hf. cbn [snd parent equiv].
    intros j k Hjk.
    destruct (equiv e0) as [ra pa mr nx] eqn:Heq0.
    unfold UnionFind.find in Hf.
    destruct (find_aux idx Eqb_idx (idx_map idx) (S mr) x pa) as [cx fp] eqn:Hfa.
    injection Hf as <- <-. cbn [parent] in Hjk.
    assert (Hclosed_pa : forall j' k', map.get pa j' = Some k' -> Sep.has_key k' pa).
    { intros j' k' Hj'k'.
      pose proof (Hc j' k') as H. rewrite Heq0 in H. cbn [parent] in H.
      exact (H Hj'k'). }
    pose proof (find_aux_maintains_parent_closed (S mr) x pa Hclosed_pa j k) as Hmc.
    rewrite Hfa in Hmc. cbn [snd] in Hmc. exact (Hmc Hjk).
  Qed.

  Local Lemma put_map_maintains_closed (pa : idx_map idx) (put_key put_val : idx) :
    (forall j k, map.get pa j = Some k -> Sep.has_key k pa) ->
    Sep.has_key put_val pa ->
    forall j k,
      map.get (map.put pa put_key put_val) j = Some k ->
      Sep.has_key k (map.put pa put_key put_val).
  Proof.
    intros Hclosed Hval j k Hjk. unfold Sep.has_key.
    pose proof (Eqb_idx_ok j put_key) as Hjpk; destruct (eqb j put_key) eqn:Hjpk_eq.
    - subst j. rewrite map.get_put_same in Hjk. injection Hjk as Hkval. subst k.
      unfold Sep.has_key in Hval.
      pose proof (Eqb_idx_ok put_val put_key) as Hpvpk; destruct (eqb put_val put_key) eqn:Hpvpk_eq.
      + subst put_val. rewrite map.get_put_same. exact I.
      + rewrite map.get_put_diff by exact Hpvpk. exact Hval.
    - rewrite map.get_put_diff in Hjk by exact Hjpk.
      pose proof (Hclosed j k Hjk) as Hk_pa. unfold Sep.has_key in Hk_pa.
      pose proof (Eqb_idx_ok k put_key) as Hkpk; destruct (eqb k put_key) eqn:Hkpk_eq.
      + subst k. rewrite map.get_put_same. exact I.
      + rewrite map.get_put_diff by exact Hkpk. exact Hk_pa.
  Qed.

  Local Lemma UnionFind_union_maintains_parent_closed
        (uf : union_find idx (idx_map idx) (idx_map nat)) (cx cy : idx) :
    (forall j k, map.get (parent uf) j = Some k -> Sep.has_key k (parent uf)) ->
    Sep.has_key cx (parent uf) ->
    Sep.has_key cy (parent uf) ->
    forall j k,
      map.get (parent (fst (UnionFind.union idx Eqb_idx (idx_map idx) (idx_map nat) uf cx cy))) j
      = Some k ->
      Sep.has_key k (parent (fst (UnionFind.union idx Eqb_idx (idx_map idx) (idx_map nat) uf cx cy))).
  Proof.
    intros Hclosed Hcx Hcy j k Hjk.
    unfold UnionFind.union in *.
    destruct (UnionFind.find uf cx) as [uf1 rx] eqn:Hucx.
    destruct (UnionFind.find uf1 cy) as [uf2 ry] eqn:Hucy. cbn in *.
    assert (Hc1 : forall j' k', map.get (parent uf1) j' = Some k' -> Sep.has_key k' (parent uf1)).
    { intros j' k' Hj'k'.
      destruct uf as [ra pa mr nx]. unfold UnionFind.find in Hucx.
      destruct (find_aux idx Eqb_idx (idx_map idx) (S mr) cx pa) as [v' f'] eqn:Hfa.
      injection Hucx as <- <-. cbn [parent] in *.
      pose proof (find_aux_maintains_parent_closed (S mr) cx pa Hclosed j' k') as IH.
      rewrite Hfa in IH. cbn [snd] in IH. exact (IH Hj'k'). }
    assert (Hc2 : forall j' k', map.get (parent uf2) j' = Some k' -> Sep.has_key k' (parent uf2)).
    { intros j' k' Hj'k'.
      destruct uf1 as [ra1 pa1 mr1 nx1]. unfold UnionFind.find in Hucy.
      destruct (find_aux idx Eqb_idx (idx_map idx) (S mr1) cy pa1) as [v1 f1] eqn:Hfa1.
      injection Hucy as <- <-. cbn [parent] in *.
      pose proof (find_aux_maintains_parent_closed (S mr1) cy pa1 Hc1 j' k') as IH.
      rewrite Hfa1 in IH. cbn [snd] in IH. exact (IH Hj'k'). }
    assert (Hrx_uf2 : Sep.has_key rx (parent uf2)).
    { pose proof (UnionFind_find_ret_haskey uf cx Hcx Hclosed) as Hrx_uf1.
      rewrite Hucx in Hrx_uf1. cbn [fst snd] in Hrx_uf1.
      pose proof (UnionFind_find_keys_preserved uf1 cy rx Hrx_uf1) as H.
      rewrite Hucy in H. cbn [fst] in H. exact H. }
    assert (Hry_uf2 : Sep.has_key ry (parent uf2)).
    { pose proof (UnionFind_find_ret_haskey uf1 cy) as Hret.
      rewrite Hucy in Hret. cbn [fst snd] in Hret.
      apply Hret.
      - pose proof (UnionFind_find_keys_preserved uf cx cy Hcy) as H.
        rewrite Hucx in H. cbn [fst] in H. exact H.
      - exact Hc1. }
    eqb_case rx ry.
    - cbn [fst parent] in Hjk. exact (Hc2 j k Hjk).
    - destruct (Nat.compare _ _); cbn [fst parent] in *;
        first
          [ exact (put_map_maintains_closed (parent uf2) ry rx Hc2 Hrx_uf2 j k Hjk)
          | exact (put_map_maintains_closed (parent uf2) rx ry Hc2 Hry_uf2 j k Hjk)
          | exact (put_map_maintains_closed (parent uf2) ry rx Hc2 Hrx_uf2 j k Hjk) ].
  Qed.

  Local Lemma Defs_union_maintains_parent_closed (x y : idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    parent_closed e0 ->
    Sep.has_key x (parent (equiv e0)) ->
    Sep.has_key y (parent (equiv e0)) ->
    parent_closed (snd (@Defs.union idx Eqb_idx symbol symbol_map idx_map idx_trie unit _ x y e0)).
  Proof.
    intros Hc Hx Hy.
    unfold Defs.union. cbn [Mbind StateMonad.state_monad].
    destruct (@Defs.find idx Eqb_idx symbol symbol_map idx_map idx_trie unit x e0)
      as [cx e1] eqn:Hf1. cbn [fst snd].
    destruct (@Defs.find idx Eqb_idx symbol symbol_map idx_map idx_trie unit y e1)
      as [cy e2] eqn:Hf2. cbn [fst snd].
    assert (Hc1 : parent_closed e1).
    { pose proof (Defs_find_maintains_parent_closed x e0 Hc) as H.
      rewrite Hf1 in H. cbn [snd] in H. exact H. }
    assert (Hc2 : parent_closed e2).
    { pose proof (Defs_find_maintains_parent_closed y e1 Hc1) as H.
      rewrite Hf2 in H. cbn [snd] in H. exact H. }
    assert (Hcx_e1 : Sep.has_key cx (parent (equiv e1))).
    { unfold Defs.find in Hf1.
      destruct (UnionFind.find (equiv e0) x) as [uf1 rxv] eqn:Huf1.
      injection Hf1 as <- <-.
      cbn [parent equiv].
      pose proof (UnionFind_find_ret_haskey (equiv e0) x Hx (fun j k Hjk => Hc j k Hjk)) as Hret.
      rewrite Huf1 in Hret. cbn [fst snd] in Hret. exact Hret. }
    assert (Hcx_e2 : Sep.has_key cx (parent (equiv e2))).
    { pose proof (Defs_find_keys_preserved y e1 cx Hcx_e1) as H.
      rewrite Hf2 in H. cbn [fst] in H. exact H. }
    assert (Hcy_e2 : Sep.has_key cy (parent (equiv e2))).
    { assert (Hy_e1 : Sep.has_key y (parent (equiv e1))).
      { pose proof (Defs_find_keys_preserved x e0 y Hy) as H.
        rewrite Hf1 in H. cbn [fst] in H. exact H. }
      unfold Defs.find in Hf2.
      destruct (UnionFind.find (equiv e1) y) as [uf2 cyv] eqn:Huf2.
      injection Hf2 as <- <-.
      cbn [parent equiv].
      pose proof (UnionFind_find_ret_haskey (equiv e1) y Hy_e1 (fun j k Hjk => Hc1 j k Hjk)) as Hret.
      rewrite Huf2 in Hret. cbn [fst snd] in Hret. exact Hret. }
    eqb_case cx cy.
    { cbn [Mret StateMonad.state_monad snd equiv parent].
      unfold parent_closed. cbn [parent equiv]. exact Hc2. }
    destruct (UnionFind.union idx Eqb_idx (idx_map idx) (idx_map nat) (equiv e2) cx cy)
      as [uf' v'] eqn:Hu.
    destruct (eqb cx v') eqn:Hcxv';
      (cbn [snd equiv parent]; unfold parent_closed; cbn [parent equiv]; intros j k Hjk;
       pose proof (UnionFind_union_maintains_parent_closed (equiv e2) cx cy
                     (fun j' k' Hj'k' => Hc2 j' k' Hj'k') Hcx_e2 Hcy_e2 j k) as Hmaint;
       rewrite Hu in Hmaint; cbn [fst parent] in Hmaint; exact (Hmaint Hjk)).
  Qed.

  (* Helper: alloc adds key fresh = fst alloc, which is not previously in parent *)
  Local Lemma alloc_fresh_key
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    Sep.has_key (fst (alloc idx idx_succ symbol symbol_map idx_map idx_trie unit e0))
                (parent (equiv (snd (alloc idx idx_succ symbol symbol_map idx_map idx_trie unit e0)))).
  Proof.
    unfold alloc.
    destruct (UnionFind.alloc idx (idx_map idx) (idx_map nat) idx_succ (equiv e0))
      as [eq' xf] eqn:Heq. cbn [fst snd parent equiv].
    unfold UnionFind.alloc in Heq.
    destruct (equiv e0) as [ra pa mr nx]. cbn in Heq. injection Heq as <- <-.
    cbn [parent]. unfold Sep.has_key. rewrite map.get_put_same. exact I.
  Qed.

  (* db_set does not change equiv: use the fact that get_analysis/update_analyses don't change equiv *)
  Local Lemma list_Mmap_get_analysis_preserves_equiv_early (args : list idx)
    (e : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    equiv (snd (list_Mmap (get_analysis idx symbol symbol_map idx_map idx_trie unit) args e)) = equiv e.
  Proof.
    induction args as [|b rest IH] in e |- *.
    - cbn. reflexivity.
    - cbn [list_Mmap].
      destruct (get_analysis idx symbol symbol_map idx_map idx_trie unit b e) as [pb eb] eqn:Hgb.
      cbn [fst snd].
      destruct (list_Mmap (get_analysis idx symbol symbol_map idx_map idx_trie unit) rest eb)
        as [pargs eargs] eqn:Hgargs.
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
      cbn beta iota. unfold Basics.compose. rewrite Hgb. cbn [fst snd].
      destruct (list_Mmap (get_analysis idx symbol symbol_map idx_map idx_trie unit) rest eb)
        as [pargs2 eargs2] eqn:Hgargs2. cbn [snd]. injection Hgargs as <- <-.
      assert (Heb : equiv eb = equiv e).
      { unfold get_analysis in Hgb.
        destruct (map.get (analyses e) b) as [a_b|] eqn:Hana.
        - cbn [snd] in Hgb. injection Hgb as <- <-. reflexivity.
        - unfold Mseq in Hgb. cbn [Mbind Mret StateMonad.state_monad fst snd] in Hgb.
          unfold Defs.update_analyses, Defs.push_worklist in Hgb. cbn [snd] in Hgb.
          injection Hgb as <- <-. reflexivity. }
      pose proof (IH eb) as IHeb. rewrite Hgargs2 in IHeb. cbn [snd] in IHeb. congruence.
  Qed.

  Local Lemma db_set_maintains_parent_closed (a : atom)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    parent_closed e0 ->
    parent_closed (snd (Defs.db_set idx Eqb_idx symbol symbol_map idx_map idx_trie unit a e0)).
  Proof.
    intro Hc. unfold parent_closed.
    unfold Defs.db_set. cbn [Mbind StateMonad.state_monad].
    unfold Defs.get_analyses.
    destruct (list_Mmap (get_analysis idx symbol symbol_map idx_map idx_trie unit)
                        (atom_args a) e0) as [p e1] eqn:Hga.
    cbn [fst snd].
    pose proof (list_Mmap_get_analysis_preserves_equiv_early (atom_args a) e0) as Hequiv1.
    rewrite Hga in Hequiv1. cbn [snd] in Hequiv1.
    destruct (Defs.update_analyses idx symbol symbol_map idx_map idx_trie unit
                (atom_ret a) (analyze idx symbol unit a p) e1) as [pu e2] eqn:Hua.
    cbn [snd]. unfold db_set'. cbn [snd equiv parent].
    intros j k Hjk.
    unfold Defs.update_analyses in Hua. cbn [snd] in Hua.
    assert (Hequiv2 : equiv e2 = equiv e1).
    { injection Hua as _ Hset. subst e2. reflexivity. }
    rewrite Hequiv2 in Hjk. rewrite Hequiv1 in Hjk.
    rewrite Hequiv2. rewrite Hequiv1. exact (Hc j k Hjk).
  Qed.

  (* rename_lookup maintains parent_closed *)
  Local Lemma rename_lookup_maintains_parent_closed (x : idx)
    (sub0 : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    parent_closed e0 ->
    parent_closed (snd (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit x sub0 e0)).
  Proof.
    intro Hc. unfold rename_lookup.
    destruct (named_list_lookup_err sub0 x) as [y|] eqn:Hlook.
    - cbn [Mret StateMonad.state_monad snd]. exact Hc.
    - cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
      cbn beta iota. unfold Basics.compose.
      destruct (alloc idx idx_succ symbol symbol_map idx_map idx_trie unit e0) as [y e1] eqn:Halloc.
      cbn [fst snd].
      pose proof (alloc_maintains_parent_closed e0 Hc) as Hc1.
      rewrite Halloc in Hc1. cbn [snd] in Hc1. exact Hc1.
  Qed.

  (* list_Mmap rename_lookup maintains parent_closed *)
  Local Lemma list_Mmap_rename_lookup_maintains_parent_closed (args : list idx) :
    forall (sub0 : named_list idx idx)
      (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit),
    parent_closed e0 ->
    parent_closed (snd (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit) args sub0 e0)).
  Proof.
    induction args as [|a args IH]; intros sub0 e0 Hc.
    - cbn. exact Hc.
    - cbn [list_Mmap].
      destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit
                  a sub0 e0) as [p e1] eqn:Hrla. destruct p as [a' sub1].
      destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                             idx_trie unit) args sub1 e1) as [p2 e2] eqn:Hrec.
      destruct p2 as [args' sub2].
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
      cbn beta iota. unfold Basics.compose. rewrite Hrla. cbn [fst snd uncurry].
      destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                             idx_trie unit) args sub1 e1) as [q e3] eqn:Hq.
      destruct q as [args2 sub3]. cbn [snd]. injection Hrec as <- <-.
      pose proof (rename_lookup_maintains_parent_closed a sub0 e0 Hc) as Hc1.
      rewrite Hrla in Hc1. cbn [snd] in Hc1.
      pose proof (IH sub1 e1 Hc1) as IHres.
      change (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit) args sub1 e1) with (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit) args sub1 e1) in IHres.
      rewrite Hq in IHres. cbn [snd] in IHres. exact IHres.
  Qed.


  (* rename_lookup result is a key of the result egraph *)
  Local Lemma rename_lookup_result_is_key (x : idx)
    (sub0 : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit)
    (sub_values_ok : forall z w, named_list_lookup_err sub0 z = Some w ->
                                  Sep.has_key w (parent (equiv e0))) :
    Sep.has_key (fst (fst (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit x sub0 e0)))
                (parent (equiv (snd (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit x sub0 e0)))).
  Proof.
    unfold rename_lookup.
    destruct (named_list_lookup_err sub0 x) as [y|] eqn:Hlook.
    - cbn [Mret StateMonad.state_monad fst snd].
      (* y = sub0[x] is a key of e0.parent *)
      exact (sub_values_ok x y Hlook).
    - cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
      cbn beta iota. unfold Basics.compose.
      destruct (alloc idx idx_succ symbol symbol_map idx_map idx_trie unit e0) as [y e1] eqn:Halloc.
      cbn [fst snd].
      pose proof (alloc_fresh_key e0) as H.
      rewrite Halloc in H. cbn [fst snd] in H. exact H.
  Qed.

  (* The key reverse direction for rename_lookup *)
  Lemma rename_lookup_haskey_in (x : idx) (sub0 : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    forall z,
      Sep.has_key z (parent (equiv (snd (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit x sub0 e0)))) ->
      Sep.has_key z (parent (equiv e0)) \/
      exists x'', named_list_lookup_err
                    (snd (fst (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit x sub0 e0))) x'' = Some z.
  Proof.
    intros z Hz. unfold rename_lookup in *.
    destruct (named_list_lookup_err sub0 x) as [y|] eqn:Hlook.
    - cbn [Mret StateMonad.state_monad fst snd] in *. left. exact Hz.
    - cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind] in Hz.
      cbn beta iota in Hz. unfold Basics.compose in Hz.
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
      cbn beta iota. unfold Basics.compose.
      destruct (alloc idx idx_succ symbol symbol_map idx_map idx_trie unit e0) as [y e1] eqn:Halloc.
      cbn [fst snd parent equiv] in Hz.
      unfold alloc in Halloc.
      destruct (UnionFind.alloc idx (idx_map idx) (idx_map nat) idx_succ (equiv e0))
        as [eq' xf] eqn:Heq.
      injection Halloc as <- <-.
      cbn [parent equiv] in Hz.
      unfold UnionFind.alloc in Heq.
      destruct (equiv e0) as [ra pa mr nx] eqn:Heq0.
      cbn in Heq. injection Heq as <- <-.
      cbn [parent] in Hz. unfold Sep.has_key in Hz.
      pose proof (Eqb_idx_ok z nx) as Hznx. destruct (eqb z nx) eqn:Hznx_eq.
      + subst z. right. exists x. cbn [fst snd]. cbn [named_list_lookup_err].
        pose proof (Eqb_idx_ok x x) as Hxx. destruct (eqb x x) eqn:Hxx_eq.
        * reflexivity.
        * exfalso. apply Hxx. reflexivity.
      + rewrite map.get_put_diff in Hz by exact Hznx.
        left. unfold Sep.has_key. cbn [parent]. exact Hz.
  Qed.

  Lemma list_Mmap_rename_lookup_haskey_in (args : list idx) :
    forall (sub0 : named_list idx idx)
      (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit)
      (z : idx),
      Sep.has_key z (parent (equiv (snd (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit) args sub0 e0)))) ->
      Sep.has_key z (parent (equiv e0)) \/
      exists x'', named_list_lookup_err
                    (snd (fst (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit) args sub0 e0))) x'' = Some z.
  Proof.
    induction args as [|a args IH]; intros sub0 e0 z Hz.
    - cbn in Hz. left. exact Hz.
    - cbn [list_Mmap] in *.
      destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit
                  a sub0 e0) as [p e1] eqn:Hrla. destruct p as [a' sub1].
      destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                             idx_trie unit) args sub1 e1) as [p2 e2] eqn:Hrec.
      destruct p2 as [args' sub2].
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind] in Hz.
      cbn beta iota in Hz. unfold Basics.compose in Hz.
      rewrite Hrla in Hz. cbn [fst snd uncurry] in Hz.
      destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                             idx_trie unit) args sub1 e1) as [q e3] eqn:Hq.
      destruct q as [args2 sub3]. cbn [snd] in Hz.
      injection Hrec as <- <-.
      specialize (IH sub1 e1 z).
      destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                             idx_trie unit) args sub1 e1) as [q' e3'] eqn:Hq'.
      destruct q' as [args2' sub3']. cbn [snd] in IH.
      assert (Heq : e3' = e3) by congruence.
      subst e3'. specialize (IH Hz). cbn [fst snd] in IH.
      destruct IH as [Hold | Hex].
      + pose proof (rename_lookup_haskey_in a sub0 e0 z) as Hhead.
        rewrite Hrla in Hhead. cbn [fst snd] in Hhead. specialize (Hhead Hold).
        cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
        cbn beta iota. unfold Basics.compose. rewrite Hrla. cbn [fst snd uncurry].
        destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                               idx_trie unit) args sub1 e1) as [qg eg] eqn:Hqg.
        destruct qg as [args_g sub_g]. cbn [snd uncurry fst].
        assert (Heqg : eg = e3) by congruence. subst eg.
        destruct Hhead as [Hold0 | Hex2].
        * left. exact Hold0.
        * destruct Hex2 as [x'' Hlook0]. right. exists x''.
          pose proof (list_Mmap_rename_lookup_sub_mono args sub1 e1 x'' z Hlook0) as Hmono.
          rewrite Hqg in Hmono. cbn [fst snd] in Hmono. exact Hmono.
      + destruct Hex as [x'' Hlook]. right. exists x''.
        cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
        cbn beta iota. unfold Basics.compose. rewrite Hrla. cbn [fst snd uncurry].
        destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                               idx_trie unit) args sub1 e1) as [qg eg] eqn:Hqg'.
        destruct qg as [args_g' sub_g']. cbn [snd uncurry fst].
        assert (Heqg : sub_g' = sub3') by congruence. subst sub_g'.
        exact Hlook.
  Qed.

  Lemma rename_atom_haskey_in (a : atom)
    (sub0 : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    forall z,
      Sep.has_key z (parent (equiv (snd (rename_atom idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit a sub0 e0)))) ->
      Sep.has_key z (parent (equiv e0)) \/
      exists x'', named_list_lookup_err
                    (snd (fst (rename_atom idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit a sub0 e0))) x'' = Some z.
  Proof.
    intro z. destruct a as [f args out]. unfold rename_atom. cbn [atom_fn atom_args atom_ret].
    cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
    cbn beta iota. unfold Basics.compose.
    destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                           idx_trie unit) args sub0 e0) as [q1 e1] eqn:Hq1.
    destruct q1 as [args' sub1]. cbn [fst snd uncurry].
    destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit
                out sub1 e1) as [q2 e2] eqn:Hq2. destruct q2 as [ret' sub2]. cbn [snd].
    intro Hz.
    pose proof (rename_lookup_haskey_in out sub1 e1 z) as Hrl.
    rewrite Hq2 in Hrl. cbn [fst snd] in Hrl. specialize (Hrl Hz).
    destruct Hrl as [Hold1 | Hex2].
    + pose proof (list_Mmap_rename_lookup_haskey_in args sub0 e0 z) as Hlm.
      specialize (Hlm (ltac:(
        destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                               idx_trie unit) args sub0 e0) as [qlm elm] eqn:Hqlm;
        cbn [snd]; assert (Heqlm : elm = e1) by congruence; subst elm; exact Hold1))).
      destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                             idx_trie unit) args sub0 e0) as [qlm elm] eqn:Hqlm.
      destruct qlm as [args_lm sub_lm]. cbn [fst snd] in Hlm.
      assert (Heqlm : elm = e1) by congruence. subst elm.
      destruct Hlm as [Hold0 | Hex1].
      * left. exact Hold0.
      * destruct Hex1 as [x'' Hlook1]. right. exists x''.
        assert (Hsub : sub_lm = sub1) by congruence. subst sub_lm.
        cbn [fst snd uncurry].
        pose proof (rename_lookup_sub_mono out sub1 e1 x'' z Hlook1) as Hmono.
        rewrite Hq2 in Hmono. cbn [fst snd] in Hmono. exact Hmono.
    + destruct Hex2 as [x'' Hlook2]. right. exists x''. exact Hlook2.
  Qed.

  (* union_keys_in: with parent_closed and keys x,y in e0,
     the result of union x y e0 has no new keys *)
  Lemma union_keys_in (x y : idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    parent_closed e0 ->
    Sep.has_key x (parent (equiv e0)) ->
    Sep.has_key y (parent (equiv e0)) ->
    forall z,
      Sep.has_key z (parent (equiv (snd (@Defs.union idx Eqb_idx symbol symbol_map idx_map idx_trie unit _ x y e0)))) ->
      Sep.has_key z (parent (equiv e0)).
  Proof.
    intros Hc Hx Hy z Hz.
    unfold Defs.union in Hz. cbn [Mbind StateMonad.state_monad] in Hz.
    destruct (@Defs.find idx Eqb_idx symbol symbol_map idx_map idx_trie unit x e0)
      as [cx e1] eqn:Hf1. cbn [fst snd] in Hz.
    destruct (@Defs.find idx Eqb_idx symbol symbol_map idx_map idx_trie unit y e1)
      as [cy e2] eqn:Hf2. cbn [fst snd] in Hz.
    assert (Hback : Sep.has_key z (parent (equiv e2)) -> Sep.has_key z (parent (equiv e0))).
    { intro Htmp.
      apply (Defs_find_keys_in x e0 z). rewrite Hf1. cbn.
      apply (Defs_find_keys_in y e1 z). rewrite Hf2. cbn. exact Htmp. }
    assert (Hc1 : parent_closed e1).
    { pose proof (Defs_find_maintains_parent_closed x e0 Hc) as Htmp. rewrite Hf1 in Htmp. cbn [snd] in Htmp. exact Htmp. }
    assert (Hc2 : parent_closed e2).
    { pose proof (Defs_find_maintains_parent_closed y e1 Hc1) as Htmp. rewrite Hf2 in Htmp. cbn [snd] in Htmp. exact Htmp. }
    eqb_case cx cy.
    { cbn [Mret StateMonad.state_monad snd equiv parent] in Hz. apply Hback. exact Hz. }
    destruct (UnionFind.union idx Eqb_idx (idx_map idx) (idx_map nat) (equiv e2) cx cy)
      as [uf' v'] eqn:Hu.
    assert (Hcx_e1 : Sep.has_key cx (parent (equiv e1))).
    { unfold Defs.find in Hf1.
      destruct (UnionFind.find (equiv e0) x) as [uf1x rxv] eqn:Huf1.
      injection Hf1 as <- <-.
      cbn [parent equiv].
      pose proof (UnionFind_find_ret_haskey (equiv e0) x Hx (fun j k Hjk => Hc j k Hjk)) as Hret.
      rewrite Huf1 in Hret. cbn [fst snd] in Hret. exact Hret. }
    assert (Hcx_e2 : Sep.has_key cx (parent (equiv e2))).
    { pose proof (Defs_find_keys_preserved y e1 cx Hcx_e1) as Htmp.
      rewrite Hf2 in Htmp. cbn [fst] in Htmp. exact Htmp. }
    assert (Hcy_e2 : Sep.has_key cy (parent (equiv e2))).
    { assert (Hy_e1 : Sep.has_key y (parent (equiv e1))).
      { pose proof (Defs_find_keys_preserved x e0 y Hy) as Htmp. rewrite Hf1 in Htmp. cbn [fst] in Htmp. exact Htmp. }
      unfold Defs.find in Hf2.
      destruct (UnionFind.find (equiv e1) y) as [uf2y cyv] eqn:Huf2.
      injection Hf2 as <- <-.
      cbn [parent equiv].
      pose proof (UnionFind_find_ret_haskey (equiv e1) y Hy_e1 (fun j k Hjk => Hc1 j k Hjk)) as Hret.
      rewrite Huf2 in Hret. cbn [fst snd] in Hret. exact Hret. }
    apply Hback.
    unfold UnionFind.union in Hu.
    destruct (UnionFind.find (equiv e2) cx) as [uf1 rx] eqn:Hucx.
    destruct (UnionFind.find uf1 cy) as [uf2 ry] eqn:Hucy. cbn in Hu.
    assert (Hc_uf1 : forall j k, map.get (parent uf1) j = Some k -> Sep.has_key k (parent uf1)).
    { intros j k Hjk.
      pose proof (Defs_find_maintains_parent_closed cx e2 Hc2) as Hc_uf1'.
      unfold Defs.find in Hc_uf1'.
      rewrite Hucx in Hc_uf1'. cbn [snd parent equiv] in Hc_uf1'.
      exact (Hc_uf1' j k Hjk). }
    assert (Hry_uf2 : Sep.has_key ry (parent uf2)).
    { pose proof (UnionFind_find_ret_haskey uf1 cy) as Hret. rewrite Hucy in Hret. cbn [fst snd] in Hret.
      apply Hret.
      - pose proof (UnionFind_find_keys_preserved (equiv e2) cx cy Hcy_e2) as Htmp2. rewrite Hucx in Htmp2. cbn [fst] in Htmp2. exact Htmp2.
      - exact Hc_uf1. }
    assert (Hrx_uf2 : Sep.has_key rx (parent uf2)).
    { pose proof (UnionFind_find_ret_haskey (equiv e2) cx Hcx_e2 (fun j k Hjk => Hc2 j k Hjk)) as Hrxe2.
      rewrite Hucx in Hrxe2. cbn [fst snd] in Hrxe2.
      pose proof (UnionFind_find_keys_preserved uf1 cy rx Hrxe2) as Htmp2. rewrite Hucy in Htmp2. cbn [fst] in Htmp2. exact Htmp2. }
    eqb_case rx ry.
    - injection Hu as <- _.
      destruct (eqb cx v') eqn:Hcxv'; cbn [snd equiv parent] in Hz.
      + apply (UnionFind_find_keys_in (equiv e2) cx z). rewrite Hucx. cbn.
        apply (UnionFind_find_keys_in uf1 cy z). rewrite Hucy. cbn. exact Hz.
      + apply (UnionFind_find_keys_in (equiv e2) cx z). rewrite Hucx. cbn.
        apply (UnionFind_find_keys_in uf1 cy z). rewrite Hucy. cbn. exact Hz.
    - destruct (Nat.compare _ _); cbn [fst parent] in *; injection Hu as <- _;
        destruct (eqb cx v') eqn:Hcxv'; cbn [snd equiv parent] in Hz;
        try (pose proof (Eqb_idx_ok z ry) as Hzry; destruct (eqb z ry) eqn:Hzry_eq;
             [subst z;
              apply (UnionFind_find_keys_in (equiv e2) cx ry); rewrite Hucx; cbn;
              apply (UnionFind_find_keys_in uf1 cy ry); rewrite Hucy; cbn; exact Hry_uf2
             |unfold Sep.has_key in Hz; rewrite map.get_put_diff in Hz by exact Hzry;
              apply (UnionFind_find_keys_in (equiv e2) cx z); rewrite Hucx; cbn;
              apply (UnionFind_find_keys_in uf1 cy z); rewrite Hucy; cbn; exact Hz]);
        try (pose proof (Eqb_idx_ok z rx) as Hzrx; destruct (eqb z rx) eqn:Hzrx_eq;
             [subst z;
              apply (UnionFind_find_keys_in (equiv e2) cx rx); rewrite Hucx; cbn;
              apply (UnionFind_find_keys_in uf1 cy rx); rewrite Hucy; cbn; exact Hrx_uf2
             |unfold Sep.has_key in Hz; rewrite map.get_put_diff in Hz by exact Hzrx;
              apply (UnionFind_find_keys_in (equiv e2) cx z); rewrite Hucx; cbn;
              apply (UnionFind_find_keys_in uf1 cy z); rewrite Hucy; cbn; exact Hz]).
  Qed.

  (* sub_values_keys: all values in sub are keys of e's equiv parent *)
  Definition sub_values_keys (sub : named_list idx idx)
    (e : Defs.instance idx symbol symbol_map idx_map idx_trie unit) : Prop :=
    forall x v, named_list_lookup_err sub x = Some v -> Sep.has_key v (parent (equiv e)).

  Local Lemma rename_lookup_maintains_sub_values_keys (x : idx)
    (sub0 : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    parent_closed e0 ->
    sub_values_keys sub0 e0 ->
    sub_values_keys
      (snd (fst (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit x sub0 e0)))
      (snd (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit x sub0 e0)).
  Proof.
    intros Hc Hsv. unfold rename_lookup.
    destruct (named_list_lookup_err sub0 x) as [y|] eqn:Hlook.
    - cbn [Mret StateMonad.state_monad fst snd].
      unfold sub_values_keys. intros z w Hlookw. exact (Hsv z w Hlookw).
    - cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
      cbn beta iota. unfold Basics.compose.
      destruct (alloc idx idx_succ symbol symbol_map idx_map idx_trie unit e0) as [fresh e1] eqn:Halloc.
      cbn [fst snd].
      unfold sub_values_keys. intros z w Hlookw. cbn [named_list_lookup_err] in Hlookw.
      pose proof (Eqb_idx_ok z x) as Hzx. destruct (eqb z x) eqn:Hzx_eq.
      + (* z = x: w = fresh *)
        subst z. injection Hlookw as <-.
        pose proof (alloc_fresh_key e0) as H. rewrite Halloc in H. cbn [fst snd] in H. exact H.
      + (* z ≠ x: w was in sub0, and sub0 values were keys of e0, hence of e1 *)
        pose proof (Hsv z w Hlookw) as Hw_e0.
        (* fresh was allocated, so e1 has all old keys plus fresh *)
        unfold alloc in Halloc.
        destruct (UnionFind.alloc idx (idx_map idx) (idx_map nat) idx_succ (equiv e0))
          as [eq' xf] eqn:Heq. injection Halloc as <- <-.
        cbn [snd parent equiv].
        unfold UnionFind.alloc in Heq.
        destruct (equiv e0) as [ra pa mr nx] eqn:Heq0. cbn in Heq. injection Heq as <- <-.
        cbn [parent]. unfold Sep.has_key in *.
        cbn [parent] in Hw_e0.
        pose proof (Eqb_idx_ok w nx) as Hwnx. destruct (eqb w nx) eqn:Hwnx_eq.
        * subst w. rewrite map.get_put_same. exact I.
        * rewrite map.get_put_diff by exact Hwnx. exact Hw_e0.
  Qed.

  Local Lemma list_Mmap_rename_lookup_maintains_sub_values_keys (args : list idx) :
    forall (sub0 : named_list idx idx)
      (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit),
    parent_closed e0 ->
    sub_values_keys sub0 e0 ->
    sub_values_keys
      (snd (fst (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit) args sub0 e0)))
      (snd (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit) args sub0 e0)).
  Proof.
    induction args as [|a args IH]; intros sub0 e0 Hc Hsv.
    - cbn. exact Hsv.
    - cbn [list_Mmap].
      destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit
                  a sub0 e0) as [p e1] eqn:Hrla. destruct p as [a' sub1].
      destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                             idx_trie unit) args sub1 e1) as [p2 e2] eqn:Hrec.
      destruct p2 as [args' sub2].
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
      cbn beta iota. unfold Basics.compose. rewrite Hrla. cbn [fst snd uncurry].
      destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                             idx_trie unit) args sub1 e1) as [q e3] eqn:Hq.
      destruct q as [args2 sub3]. cbn [snd uncurry]. injection Hrec as <- <-.
      pose proof (rename_lookup_maintains_sub_values_keys a sub0 e0 Hc Hsv) as Hsv1.
      rewrite Hrla in Hsv1. cbn [fst snd] in Hsv1.
      pose proof (rename_lookup_maintains_parent_closed a sub0 e0 Hc) as Hc1.
      rewrite Hrla in Hc1. cbn [snd] in Hc1.
      pose proof (IH sub1 e1 Hc1 Hsv1) as IHres.
      change (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit) args sub1 e1) with (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit) args sub1 e1) in IHres.
      rewrite Hq in IHres. cbn [fst snd] in IHres. exact IHres.
  Qed.

  Local Lemma rename_atom_maintains_sub_values_keys (a : atom)
    (sub0 : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    parent_closed e0 ->
    sub_values_keys sub0 e0 ->
    sub_values_keys
      (snd (fst (rename_atom idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit a sub0 e0)))
      (snd (rename_atom idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit a sub0 e0)).
  Proof.
    intros Hc Hsv. destruct a as [f args out]. unfold rename_atom. cbn [atom_fn atom_args atom_ret].
    cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
    cbn beta iota. unfold Basics.compose.
    destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                           idx_trie unit) args sub0 e0) as [q1 e1] eqn:Hq1.
    destruct q1 as [args' sub1]. cbn [fst snd uncurry].
    destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit
                out sub1 e1) as [q2 e2] eqn:Hq2. destruct q2 as [ret' sub2]. cbn [snd].
    (* sub_values_keys sub1 e1 *)
    assert (Hsv1 : sub_values_keys sub1 e1).
    { pose proof (list_Mmap_rename_lookup_maintains_sub_values_keys args sub0 e0 Hc Hsv) as H.
      destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit) args sub0 e0) as [qH eH] eqn:HqH.
      destruct qH as [aH sH]. cbn [snd fst] in H.
      assert (HeH : eH = e1) by congruence.
      assert (HsH : sH = sub1) by congruence.
      subst eH. subst sH. exact H. }
    (* parent_closed e1 *)
    assert (Hce1 : parent_closed e1).
    { pose proof (list_Mmap_rename_lookup_maintains_parent_closed args sub0 e0 Hc) as H.
      destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit) args sub0 e0) as [qH eH] eqn:HqH.
      cbn [snd] in H.
      assert (HeH : eH = e1) by congruence. subst eH. exact H. }
    pose proof (rename_lookup_maintains_sub_values_keys out sub1 e1 Hce1 Hsv1) as Hsv2.
    change (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit out sub1 e1) with (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit out sub1 e1) in Hsv2.
    rewrite Hq2 in Hsv2. cbn [fst snd] in Hsv2. exact Hsv2.
  Qed.

  (* db_values_in_sub: all DB entry values appear as values in sub *)
  Definition db_values_in_sub (sub : named_list idx idx)
    (e : Defs.instance idx symbol symbol_map idx_map idx_trie unit) : Prop :=
    forall f tbl args dbent,
      map.get (db e) f = Some tbl ->
      map.get tbl args = Some dbent ->
      exists x'', named_list_lookup_err sub x'' = Some (entry_value idx unit dbent).

  (* alloc doesn't change db *)
  Local Lemma alloc_maintains_db_values_in_sub (sub : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    db_values_in_sub sub e0 ->
    db_values_in_sub sub (snd (alloc idx idx_succ symbol symbol_map idx_map idx_trie unit e0)).
  Proof.
    intro Hdv. unfold db_values_in_sub.
    rewrite alloc_preserves_db_val. exact Hdv.
  Qed.

  Local Lemma rename_lookup_maintains_db_values_in_sub (x : idx) (sub0 : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    db_values_in_sub sub0 e0 ->
    db_values_in_sub
      (snd (fst (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit x sub0 e0)))
      (snd (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit x sub0 e0)).
  Proof.
    intro Hdv. unfold rename_lookup.
    destruct (named_list_lookup_err sub0 x) as [y|] eqn:Hlook.
    - cbn [Mret StateMonad.state_monad fst snd]. exact Hdv.
    - cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
      cbn beta iota. unfold Basics.compose.
      destruct (alloc idx idx_succ symbol symbol_map idx_map idx_trie unit e0) as [fresh e1] eqn:Halloc.
      cbn [fst snd].
      pose proof (alloc_maintains_db_values_in_sub sub0 e0 Hdv) as Hdv1.
      rewrite Halloc in Hdv1. cbn [snd] in Hdv1.
      (* sub1 = (x,fresh)::sub0. need to show db_values_in_sub ((x,fresh)::sub0) e1 *)
      unfold db_values_in_sub in *. intros f tbl args entry Hf Ha.
      specialize (Hdv1 f tbl args entry Hf Ha) as [x'' Hlook'].
      exists x''. cbn [named_list_lookup_err].
      pose proof (Eqb_idx_ok x'' x) as Hxx'. destruct (eqb x'' x) eqn:Hxx'_eq.
      + (* x'' = x: but then sub0[x] = Some fresh from Hlook, but Hlook' is sub0[x''] = Some v *)
        (* sub1 = (x, fresh)::sub0, so named_list_lookup_err ((x,fresh)::sub0) x'' = Some fresh *)
        (* But fresh might ≠ entry_value. We need the ORIGINAL x'' from sub0 *)
        (* Since eqb x'' x = true, x'' = x. And sub0[x] = None (Hlook). But Hlook' says sub0[x''] = Some v.
           With x'' = x, sub0[x] = Some v. But Hlook says sub0[x] = None. Contradiction! *)
        subst x''. rewrite Hlook in Hlook'. discriminate.
      + exact Hlook'.
  Qed.

  Local Lemma list_Mmap_rename_lookup_maintains_db_values_in_sub (args : list idx) :
    forall (sub0 : named_list idx idx)
      (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit),
    db_values_in_sub sub0 e0 ->
    db_values_in_sub
      (snd (fst (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit) args sub0 e0)))
      (snd (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit) args sub0 e0)).
  Proof.
    induction args as [|a args IH]; intros sub0 e0 Hdv.
    - cbn. exact Hdv.
    - cbn [list_Mmap].
      destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit
                  a sub0 e0) as [p e1] eqn:Hrla. destruct p as [a' sub1].
      destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                             idx_trie unit) args sub1 e1) as [p2 e2] eqn:Hrec.
      destruct p2 as [args' sub2].
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
      cbn beta iota. unfold Basics.compose. rewrite Hrla. cbn [fst snd uncurry].
      destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                             idx_trie unit) args sub1 e1) as [q e3] eqn:Hq.
      destruct q as [args2 sub3]. cbn [snd uncurry]. injection Hrec as <- <-.
      pose proof (rename_lookup_maintains_db_values_in_sub a sub0 e0 Hdv) as Hdv1.
      rewrite Hrla in Hdv1. cbn [fst snd] in Hdv1.
      pose proof (IH sub1 e1 Hdv1) as IHres.
      change (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit) args sub1 e1) with (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit) args sub1 e1) in IHres.
      rewrite Hq in IHres. cbn [snd] in IHres. exact IHres.
  Qed.

  Local Lemma union_maintains_db_values_in_sub (sub : named_list idx idx) (x y : idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    db_values_in_sub sub e0 ->
    db_values_in_sub sub (snd (@Defs.union idx Eqb_idx symbol symbol_map idx_map idx_trie unit _ x y e0)).
  Proof.
    intro Hdv. unfold db_values_in_sub in *.
    intros f tbl args entry Hf Ha.
    apply (Hdv f tbl args entry).
    - rewrite <- (union_preserves_db_val x y e0). rewrite Hf. reflexivity.
    - exact Ha.
  Qed.

  (* db_set stores (atom_ret a) in the DB *)
  Local Lemma db_set_adds_db_values_in_sub (a : atom) (sub : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    db_values_in_sub sub e0 ->
    (exists x'', named_list_lookup_err sub x'' = Some (atom_ret a)) ->
    db_values_in_sub sub (snd (Defs.db_set idx Eqb_idx symbol symbol_map idx_map idx_trie unit a e0)).
  Proof.
    intros Hdv [x'' Hlook].
    unfold db_values_in_sub. intros f tbl args dbent Hf Ha.
    (* Use db_set_atom_in_db_inv: any entry b after db_set a is either a or was in old db *)
    pose proof (db_set_atom_in_db_inv a (Build_atom f args (entry_value idx unit dbent)) e0) as Hinv.
    unfold atom_in_db, Is_Some_satisfying in Hinv. cbn [atom_fn atom_args atom_ret] in Hinv.
    assert (Hb : Semantics.atom_in_db idx symbol symbol_map idx_trie unit
                   (Build_atom f args (entry_value idx unit dbent))
                   (db (snd (Defs.db_set idx Eqb_idx symbol symbol_map idx_map idx_trie unit a e0)))).
    { unfold atom_in_db, Is_Some_satisfying. cbn [atom_fn atom_args atom_ret].
      rewrite Hf. cbn [Is_Some_satisfying].
      rewrite Ha. cbn [Is_Some_satisfying]. reflexivity. }
    specialize (Hinv Hb).
    destruct Hinv as [Hmatch | Hold].
    - (* b = a *)
      destruct Hmatch as [Hfn Hmatch2]. destruct Hmatch2 as [Harg Hret].
      cbn [atom_fn atom_args atom_ret] in Hret.
      rewrite Hret. exists x''. exact Hlook.
    - (* b was in old db: extract its tbl/entry and apply Hdv *)
      unfold atom_in_db, Semantics.atom_in_db, Is_Some_satisfying in Hold.
      cbn [atom_fn atom_args atom_ret] in Hold.
      destruct (map.get (db e0) f) as [tbl0|] eqn:Hf0; [|contradiction].
      cbn [Is_Some_satisfying] in Hold.
      destruct (map.get tbl0 args) as [entry0|] eqn:Ha0; [|contradiction].
      cbn [Is_Some_satisfying entry_value] in Hold.
      pose proof (Hdv f tbl0 args entry0 Hf0 Ha0) as [x''' Hlook''].
      exists x'''. rewrite <- Hold. exact Hlook''.
  Qed.

  (* update_entry maintains db_values_in_sub, given atom_ret a is in sub *)
  Local Lemma update_entry_maintains_db_values_in_sub (a : atom) (sub : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    db_values_in_sub sub e0 ->
    (exists x'', named_list_lookup_err sub x'' = Some (atom_ret a)) ->
    db_values_in_sub sub (snd (update_entry a e0)).
  Proof.
    intros Hdv Hret.
    unfold update_entry. cbn [Mbind StateMonad.state_monad].
    destruct (Defs.db_lookup idx symbol symbol_map idx_map idx_trie unit
                (atom_fn a) (atom_args a) e0) as [mout e0'] eqn:Hlu.
    cbn [fst snd].
    assert (He0' : e0' = e0).
    { unfold Defs.db_lookup in Hlu. cbn in Hlu. injection Hlu as _ <-. reflexivity. }
    subst e0'. destruct mout as [r|].
    - (* Some r: union r (atom_ret a); union doesn't change db *)
      cbn [Mseq Mbind Mret StateMonad.state_monad snd].
      destruct (@Defs.union idx Eqb_idx symbol symbol_map idx_map idx_trie unit _ r (atom_ret a) e0) as [v_u e_u] eqn:Hu_res.
      cbn [snd].
      unfold db_values_in_sub. intros f tbl args dbent2 Hf2 Ha2.
      apply (Hdv f tbl args dbent2).
      + pose proof (union_preserves_db_val r (atom_ret a) e0) as Hdbval. rewrite Hu_res in Hdbval. cbn [snd] in Hdbval.
        rewrite <- Hdbval. exact Hf2.
      + exact Ha2.
    - (* None: db_set a *)
      cbn [Mret StateMonad.state_monad snd].
      exact (db_set_adds_db_values_in_sub a sub e0 Hdv Hret).
  Qed.

  (* update_entry maintains parent_closed, given sufficient invariants *)
  Local Lemma update_entry_maintains_parent_closed (a : atom)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    parent_closed e0 ->
    sub_values_keys ([] : named_list idx idx) e0 ->  (* dummy: use actual sub *)
    Sep.has_key (atom_ret a) (parent (equiv e0)) ->
    forall sub, sub_values_keys sub e0 -> db_values_in_sub sub e0 ->
    parent_closed (snd (update_entry a e0)).
  Proof.
    intros Hc _ Hret sub Hsv Hdv.
    unfold update_entry. cbn [Mbind StateMonad.state_monad].
    destruct (Defs.db_lookup idx symbol symbol_map idx_map idx_trie unit
                (atom_fn a) (atom_args a) e0) as [mout e0'] eqn:Hlu.
    cbn [fst snd].
    assert (He0' : e0' = e0).
    { unfold Defs.db_lookup in Hlu. cbn in Hlu. injection Hlu as _ <-. reflexivity. }
    subst e0'. destruct mout as [r|].
    - (* Some r: union r (atom_ret a) *)
      cbn [Mseq Mbind Mret StateMonad.state_monad snd].
      (* r from db_lookup: r is in sub (by db_values_in_sub) and sub values are keys (by sub_values_keys) *)
      assert (Hr_key : Sep.has_key r (parent (equiv e0))).
      { unfold Defs.db_lookup in Hlu. cbn in Hlu.
        destruct (map.get (db e0) (atom_fn a)) as [tbl|] eqn:Htbl; [|discriminate].
        cbn in Hlu.
        destruct (map.get tbl (atom_args a)) as [entry|] eqn:Hentry; [|discriminate].
        cbn in Hlu. injection Hlu as Hlu.
        specialize (Hdv (atom_fn a) tbl (atom_args a) entry Htbl Hentry) as [x'' Hlook].
        rewrite <- Hlu.
        exact (Hsv x'' (entry_value idx unit entry) Hlook). }
      destruct (@Defs.union idx Eqb_idx symbol symbol_map idx_map idx_trie unit _ r (atom_ret a) e0) as [v_u e_u] eqn:Hu_union.
      cbn [snd].
      pose proof (Defs_union_maintains_parent_closed r (atom_ret a) e0 Hc Hr_key Hret) as Hmaint.
      rewrite Hu_union in Hmaint. cbn [snd] in Hmaint. exact Hmaint.
    - (* None: db_set — equiv unchanged *)
      cbn [Mret StateMonad.state_monad snd].
      exact (db_set_maintains_parent_closed a e0 Hc).
  Qed.

  (* rename_atom maintains db_values_in_sub *)
  Local Lemma rename_atom_maintains_db_values_in_sub (a : atom)
    (sub0 : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    db_values_in_sub sub0 e0 ->
    db_values_in_sub
      (snd (fst (rename_atom idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit a sub0 e0)))
      (snd (rename_atom idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit a sub0 e0)).
  Proof.
    intro Hdv. destruct a as [f args out]. unfold rename_atom. cbn [atom_fn atom_args atom_ret].
    cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
    cbn beta iota. unfold Basics.compose.
    destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                           idx_trie unit) args sub0 e0) as [q1 e1] eqn:Hq1.
    destruct q1 as [args' sub1]. cbn [fst snd uncurry].
    destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit
                out sub1 e1) as [q2 e2] eqn:Hq2. destruct q2 as [ret' sub2]. cbn [snd].
    pose proof (list_Mmap_rename_lookup_maintains_db_values_in_sub args sub0 e0 Hdv) as Hdv1.
    destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                           idx_trie unit) args sub0 e0) as [qH1 eH1] eqn:HqH1.
    destruct qH1 as [aH1 sH1]. cbn [fst snd] in Hdv1.
    assert (HeH1 : eH1 = e1) by congruence. assert (HsH1 : sH1 = sub1) by congruence.
    subst eH1. subst sH1.
    pose proof (rename_lookup_maintains_db_values_in_sub out sub1 e1 Hdv1) as Hdv2.
    change (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit out sub1 e1) with (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit out sub1 e1) in Hdv2.
    rewrite Hq2 in Hdv2. cbn [fst snd] in Hdv2. exact Hdv2.
  Qed.

  (* atom_ret a' is in sub after rename_atom *)
  Local Lemma rename_atom_ret_in_sub (a : atom) (sub0 : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit)
    {a' sub1 e1} (Hra : rename_atom idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit a sub0 e0 = ((a', sub1), e1)) :
    exists x'', named_list_lookup_err sub1 x'' = Some (atom_ret a').
  Proof.
    destruct a as [f args out]. unfold rename_atom in Hra. cbn [atom_fn atom_args atom_ret] in Hra.
    cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind] in Hra.
    cbn beta iota in Hra. unfold Basics.compose in Hra.
    destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                           idx_trie unit) args sub0 e0) as [q1 emid] eqn:Hq1.
    destruct q1 as [args'' submid]. cbn [fst snd uncurry] in Hra.
    destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit
                out submid emid) as [q2 e2'] eqn:Hq2. destruct q2 as [ret' sub2']. cbn [snd] in Hra.
    injection Hra as <- <- <-.
    (* Now: a' = Build_atom f args'' ret', sub1 = sub2', e1 = e2' *)
    (* Need: exists x'', sub2'[x''] = Some ret' = Some (atom_ret a') *)
    cbn [atom_ret].
    unfold rename_lookup in Hq2.
    destruct (named_list_lookup_err submid out) as [y|] eqn:Hlook.
    - cbn [Mret StateMonad.state_monad] in Hq2. injection Hq2 as <- <- <-.
      exists out. exact Hlook.
    - cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind] in Hq2.
      cbn beta iota in Hq2. unfold Basics.compose in Hq2.
      destruct (alloc idx idx_succ symbol symbol_map idx_map idx_trie unit emid) as [fresh e2''] eqn:Halloc.
      cbn [fst snd] in Hq2. injection Hq2 as <- <- <-.
      cbn [named_list_lookup_err].
      pose proof (Eqb_idx_ok out out) as Hoo. destruct (eqb out out) eqn:Hoo_eq.
      + exists out. rewrite Hoo_eq. reflexivity.
      + exfalso. apply Hoo. reflexivity.
  Qed.

  (* Helper to get parent_closed from rename_atom chain *)
  Local Lemma rename_atom_maintains_parent_closed (a : atom) (sub0 : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    parent_closed e0 ->
    parent_closed (snd (rename_atom idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit a sub0 e0)).
  Proof.
    intro Hc. destruct a as [f args out]. unfold rename_atom. cbn [atom_fn atom_args atom_ret].
    cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
    cbn beta iota. unfold Basics.compose.
    destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                           idx_trie unit) args sub0 e0) as [q1 e1] eqn:Hq1.
    destruct q1 as [args' sub1]. cbn [fst snd uncurry].
    destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit
                out sub1 e1) as [q2 e2] eqn:Hq2. destruct q2 as [ret' sub2]. cbn [snd].
    pose proof (rename_lookup_maintains_parent_closed out sub1 e1) as Hc2.
    rewrite Hq2 in Hc2. cbn [snd] in Hc2. apply Hc2.
    (* parent_closed e1 from list_Mmap *)
    (* Use list_Mmap_rename_lookup_maintains_parent_closed *)
    pose proof (list_Mmap_rename_lookup_maintains_parent_closed args sub0 e0 Hc) as Hce1.
    destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit) args sub0 e0) as [qH eH] eqn:HqH.
    cbn [snd] in Hce1.
    assert (HeH : eH = e1) by congruence. subst eH. exact Hce1.
  Qed.

  (* The key theorem: with strengthened invariant *)
  Lemma clauses_to_instance_haskey_in_sub
    (cs : list (Semantics.clause idx symbol))
    (sub0 : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit)
    (z : idx) :
    parent_closed e0 ->
    sub_values_keys sub0 e0 ->
    db_values_in_sub sub0 e0 ->
    match clauses_to_instance idx_succ (analysis_result:=unit) cs sub0 e0 with
    | (_, sub1, e1) =>
        Sep.has_key z (parent (equiv e1)) ->
        Sep.has_key z (parent (equiv e0)) \/
        (exists x', named_list_lookup_err sub1 x' = Some z)
    end.
  Proof.
    revert sub0 e0.
    induction cs as [|c cs IH]; intros sub0 e0 Hc Hsv Hdv.
    - cbn. intro H. left. exact H.
    - cbn [Semantics.clauses_to_instance list_Miter].
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mseq Mbind Mret].
      cbn beta iota. unfold Basics.compose.
      destruct (add_clause_to_instance idx Eqb_idx idx_succ symbol symbol_map
                  idx_map idx_trie unit c sub0 e0) as [q e1] eqn:Hadd.
      destruct q as [u sub1]. cbn [snd uncurry].
      destruct (clauses_to_instance idx_succ (analysis_result:=unit) cs sub1 e1) as [p_fin e_fin] eqn:Hfin.
      destruct p_fin as [u_fin sub_fin].
      intro Hz.
      (* Apply IH: need parent_closed e1, sub_values_keys sub1 e1, db_values_in_sub sub1 e1 *)
      (* First, compute these from add_clause *)
      assert (Hce1_sv1_dv1 :
        parent_closed e1 /\ sub_values_keys sub1 e1 /\ db_values_in_sub sub1 e1).
      { destruct c as [x y | a_clause].
        - (* eq_clause x y *)
          unfold add_clause_to_instance in Hadd.
          cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind] in Hadd.
          cbn beta iota in Hadd. unfold Basics.compose in Hadd.
          destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit
                      x sub0 e0) as [p1 e1'] eqn:Hrx. destruct p1 as [x' sub1'].
          cbn [fst snd uncurry] in Hadd.
          destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit
                      y sub1' e1') as [p2 e2'] eqn:Hry. destruct p2 as [y' sub2'].
          cbn [fst snd uncurry] in Hadd.
          cbn [lift StateMonad.state_monad Mbind Mret fst snd] in Hadd.
          cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mseq Mbind Mret] in Hadd.
          cbn beta iota in Hadd. unfold Basics.compose in Hadd.
          destruct (Defs.union x' y' e2') as [v e3'] eqn:Hu. cbn [uncurry fst snd] in Hadd.
          injection Hadd as <- <- <-.
          assert (Hce1' : parent_closed e1').
          { pose proof (rename_lookup_maintains_parent_closed x sub0 e0 Hc). rewrite Hrx in H. cbn [snd] in H. exact H. }
          assert (Hce2' : parent_closed e2').
          { pose proof (rename_lookup_maintains_parent_closed y sub1' e1' Hce1'). rewrite Hry in H. cbn [snd] in H. exact H. }
          assert (Hsv1' : sub_values_keys sub1' e1').
          { pose proof (rename_lookup_maintains_sub_values_keys x sub0 e0 Hc Hsv). rewrite Hrx in H. cbn [fst snd] in H. exact H. }
          assert (Hsv2' : sub_values_keys sub2' e2').
          { pose proof (rename_lookup_maintains_sub_values_keys y sub1' e1' Hce1' Hsv1'). rewrite Hry in H. cbn [fst snd] in H. exact H. }
          assert (Hx'_key : Sep.has_key x' (parent (equiv e2'))).
          { pose proof (rename_lookup_result_is_key x sub0 e0 Hsv) as Hxkey.
            rewrite Hrx in Hxkey. cbn [fst snd] in Hxkey.
            unfold rename_lookup in Hry.
            destruct (named_list_lookup_err sub1' y) as [yv|] eqn:Hlooky.
            - cbn [Mret StateMonad.state_monad] in Hry. injection Hry as <- <- <-. exact Hxkey.
            - cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind] in Hry.
              cbn beta iota in Hry. unfold Basics.compose in Hry.
              destruct (alloc idx idx_succ symbol symbol_map idx_map idx_trie unit e1') as [fresh2 e2''] eqn:Halloc.
              cbn [fst snd] in Hry. injection Hry as <- <- <-.
              unfold alloc in Halloc.
              destruct (UnionFind.alloc idx (idx_map idx) (idx_map nat) idx_succ (equiv e1')) as [eq' xf2] eqn:Heq.
              injection Halloc as <- <-.
              cbn [parent equiv].
              unfold UnionFind.alloc in Heq.
              destruct (equiv e1') as [ra pa mr nx] eqn:Heq0.
              cbn in Heq. injection Heq as <- <-.
              cbn [parent]. unfold Sep.has_key in *.
              cbn [parent] in Hxkey.
              pose proof (Eqb_idx_ok x' nx) as Hx'nx. destruct (eqb x' nx) eqn:Hx'nx_eq.
              + subst x'. rewrite map.get_put_same. exact I.
              + rewrite map.get_put_diff by exact Hx'nx. exact Hxkey. }
          assert (Hy'_key : Sep.has_key y' (parent (equiv e2'))).
          { pose proof (rename_lookup_result_is_key y sub1' e1' Hsv1'). rewrite Hry in H. cbn [fst snd] in H. exact H. }
          assert (Hce3' : parent_closed e3').
          { pose proof (Defs_union_maintains_parent_closed x' y' e2' Hce2' Hx'_key Hy'_key) as Hmaint.
            rewrite Hu in Hmaint. cbn [snd] in Hmaint. exact Hmaint. }
          (* sub_values_keys sub2' e3': union doesn't change which values are keys (only merges reps) *)
          assert (Hsv3' : sub_values_keys sub2' e3').
          { unfold sub_values_keys. intros x'' val Hlookv.
            specialize (Hsv2' x'' val Hlookv).
            pose proof (union_extends_keys x' y' e2') as Hext.
            specialize (Hext val Hsv2').
            rewrite Hu in Hext. cbn [snd equiv parent] in Hext. exact Hext. }
          (* db_values_in_sub: union doesn't change db *)
          assert (Hdv3' : db_values_in_sub sub2' e3').
          { pose proof (rename_lookup_maintains_db_values_in_sub x sub0 e0 Hdv). rewrite Hrx in H. cbn [fst snd] in H.
            pose proof (rename_lookup_maintains_db_values_in_sub y sub1' e1' H). rewrite Hry in H0. cbn [fst snd] in H0.
            pose proof (union_maintains_db_values_in_sub sub2' x' y' e2' H0) as Hdvu.
            rewrite Hu in Hdvu. cbn [snd] in Hdvu. exact Hdvu. }
          refine (conj Hce3' (conj Hsv3' Hdv3')).
        - (* atom_clause a_clause *)
          unfold add_clause_to_instance in Hadd.
          cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind] in Hadd.
          cbn beta iota in Hadd. unfold Basics.compose in Hadd.
          destruct (rename_atom idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit
                      a_clause sub0 e0) as [p1 e1'] eqn:Hra. destruct p1 as [a' sub1'].
          cbn [fst snd uncurry] in Hadd.
          cbn [lift StateMonad.state_monad Mbind Mret fst snd] in Hadd.
          cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mseq Mbind Mret] in Hadd.
          cbn beta iota in Hadd. unfold Basics.compose in Hadd.
          destruct (update_entry a' e1') as [u' e2'] eqn:Hue. cbn [uncurry fst snd] in Hadd.
          injection Hadd as <- <- <-.
          assert (Hce1' : parent_closed e1').
          { pose proof (rename_atom_maintains_parent_closed a_clause sub0 e0 Hc) as H.
            rewrite Hra in H. cbn [snd] in H. exact H. }
          assert (Hsv1' : sub_values_keys sub1' e1').
          { pose proof (rename_atom_maintains_sub_values_keys a_clause sub0 e0 Hc Hsv) as H.
            rewrite Hra in H. cbn [fst snd] in H. exact H. }
          assert (Hdv1' : db_values_in_sub sub1' e1').
          { pose proof (rename_atom_maintains_db_values_in_sub a_clause sub0 e0 Hdv) as H.
            rewrite Hra in H. cbn [fst snd] in H. exact H. }
          assert (Hret_in_sub : exists x'', named_list_lookup_err sub1' x'' = Some (atom_ret a')).
          { exact (rename_atom_ret_in_sub a_clause sub0 e0 Hra). }
          assert (Hret_key : Sep.has_key (atom_ret a') (parent (equiv e1'))).
          { destruct Hret_in_sub as [x'' Hlook]. exact (Hsv1' x'' (atom_ret a') Hlook). }
          assert (Hce2' : parent_closed e2').
          { assert (Hdummy : sub_values_keys ([] : named_list idx idx) e1').
            { unfold sub_values_keys. intros x v H. cbn in H. discriminate. }
            pose proof (update_entry_maintains_parent_closed a' e1' Hce1'
              Hdummy Hret_key sub1' Hsv1' Hdv1') as H.
            rewrite Hue in H. cbn [snd] in H. exact H. }
          assert (Hsv2' : sub_values_keys sub1' e2').
          { unfold sub_values_keys. intros x'' v Hlookv. specialize (Hsv1' x'' v Hlookv).
            (* v was a key of e1'. Need to show it's a key of e2'.
               update_entry = db_set or union. Both preserve keys or extend them. *)
            (* For db_set: equiv unchanged. For union: union extends keys. *)
            unfold update_entry in Hue.
            cbn [Mbind StateMonad.state_monad] in Hue.
            destruct (Defs.db_lookup idx symbol symbol_map idx_map idx_trie unit
                        (atom_fn a') (atom_args a') e1') as [mout e0'] eqn:Hlu.
            assert (He0' : e0' = e1').
            { unfold Defs.db_lookup in Hlu. cbn in Hlu. injection Hlu as _ <-. reflexivity. }
            subst e0'. destruct mout as [r|].
            - cbn [Mseq Mbind Mret StateMonad.state_monad snd] in Hue.
              destruct (Defs.union r (atom_ret a') e1') as [vv_u e_union] eqn:Hunion.
              injection Hue as <- ->.
              pose proof (union_extends_keys r (atom_ret a') e1') as Hext.
              specialize (Hext v Hsv1').
              rewrite Hunion in Hext. cbn [snd equiv parent] in Hext. exact Hext.
            - cbn [Mret StateMonad.state_monad snd] in Hue.
              (* db_set only changes db, not equiv. *)
              (* Show equiv e2' = equiv e1' via Hue and db_set unfolding *)
              unfold Defs.db_set in Hue. cbn [Mbind StateMonad.state_monad] in Hue.
              unfold Defs.get_analyses in Hue.
              destruct (list_Mmap (get_analysis idx symbol symbol_map idx_map idx_trie unit)
                                  (atom_args a') e1') as [pp e11] eqn:Hgg.
              cbn [fst snd] in Hue.
              destruct (Defs.update_analyses idx symbol symbol_map idx_map idx_trie unit
                          (atom_ret a') (analyze idx symbol unit a' pp) e11) as [pu e22] eqn:Huu.
              cbn [snd] in Hue. unfold db_set' in Hue. cbn [snd] in Hue.
              injection Hue as _ He2'.
              rewrite <- He2'. cbn [equiv parent].
              pose proof (list_Mmap_get_analysis_preserves_equiv_early (atom_args a') e1') as Heq1.
              rewrite Hgg in Heq1. cbn [snd] in Heq1.
              unfold Defs.update_analyses in Huu. cbn [snd] in Huu. injection Huu as _ He22.
              rewrite <- He22. rewrite Heq1. exact Hsv1'. }
          assert (Hdv2' : db_values_in_sub sub1' e2').
          { pose proof (update_entry_maintains_db_values_in_sub a' sub1' e1' Hdv1' Hret_in_sub) as H.
            rewrite Hue in H. cbn [snd] in H. exact H. }
          refine (conj Hce2' (conj Hsv2' Hdv2')). }
      destruct Hce1_sv1_dv1 as [Hce1 Hrest]. destruct Hrest as [Hsv1 Hdv1].
      (* Apply IH *)
      pose proof (IH sub1 e1 Hce1 Hsv1 Hdv1) as IH_inst.
      change (clauses_to_instance idx_succ cs sub1 e1) with (clauses_to_instance idx_succ cs sub1 e1) in IH_inst.
      rewrite Hfin in IH_inst. cbn [snd] in IH_inst.
      specialize (IH_inst Hz).
      destruct IH_inst as [Hz1 | Hex'].
      + (* z was in e1 = snd(add_clause) — now go backward to e0 *)
        destruct c as [x y | a_clause].
        * (* eq_clause x y *)
          unfold add_clause_to_instance in Hadd.
          cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind] in Hadd.
          cbn beta iota in Hadd. unfold Basics.compose in Hadd.
          destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit
                      x sub0 e0) as [p1 e1'] eqn:Hrx. destruct p1 as [x' sub1'].
          cbn [fst snd uncurry] in Hadd.
          destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit
                      y sub1' e1') as [p2 e2'] eqn:Hry. destruct p2 as [y' sub2'].
          cbn [fst snd uncurry] in Hadd.
          cbn [lift StateMonad.state_monad Mbind Mret fst snd] in Hadd.
          cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mseq Mbind Mret] in Hadd.
          cbn beta iota in Hadd. unfold Basics.compose in Hadd.
          destruct (Defs.union x' y' e2') as [v e3'] eqn:Hu. cbn [uncurry fst snd] in Hadd.
          injection Hadd as <- <- <-.
          (* Hz1 : has_key z e3' = snd(union x' y' e2') *)
          assert (Hce1' : parent_closed e1').
          { pose proof (rename_lookup_maintains_parent_closed x sub0 e0 Hc). rewrite Hrx in H. cbn [snd] in H. exact H. }
          assert (Hce2' : parent_closed e2').
          { pose proof (rename_lookup_maintains_parent_closed y sub1' e1' Hce1'). rewrite Hry in H. cbn [snd] in H. exact H. }
          assert (Hx'_key : Sep.has_key x' (parent (equiv e2'))).
          { pose proof (rename_lookup_result_is_key x sub0 e0 Hsv) as Hxkey.
            rewrite Hrx in Hxkey. cbn [fst snd] in Hxkey.
            unfold rename_lookup in Hry.
            destruct (named_list_lookup_err sub1' y) as [yv|] eqn:Hlooky.
            - cbn [Mret StateMonad.state_monad] in Hry. injection Hry as <- <- <-. exact Hxkey.
            - cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind] in Hry.
              cbn beta iota in Hry. unfold Basics.compose in Hry.
              destruct (alloc idx idx_succ symbol symbol_map idx_map idx_trie unit e1') as [fresh2 e2''] eqn:Halloc.
              cbn [fst snd] in Hry. injection Hry as <- <- <-.
              unfold alloc in Halloc.
              destruct (UnionFind.alloc idx (idx_map idx) (idx_map nat) idx_succ (equiv e1')) as [eq' xf2] eqn:Heq.
              injection Halloc as <- <-.
              cbn [parent equiv].
              unfold UnionFind.alloc in Heq.
              destruct (equiv e1') as [ra pa mr nx] eqn:Heq0.
              cbn in Heq. injection Heq as <- <-.
              cbn [parent]. unfold Sep.has_key in *.
              cbn [parent] in Hxkey.
              pose proof (Eqb_idx_ok x' nx) as Hx'nx. destruct (eqb x' nx) eqn:Hx'nx_eq.
              + subst x'. rewrite map.get_put_same. exact I.
              + rewrite map.get_put_diff by exact Hx'nx. exact Hxkey. }
          assert (Hy'_key : Sep.has_key y' (parent (equiv e2'))).
          { pose proof (rename_lookup_maintains_sub_values_keys x sub0 e0 Hc Hsv). rewrite Hrx in H. cbn [fst snd] in H.
            pose proof (rename_lookup_result_is_key y sub1' e1' H). rewrite Hry in H0. cbn [fst snd] in H0. exact H0. }
          (* union backward: has_key z e3' -> has_key z e2' *)
          pose proof (union_keys_in x' y' e2' Hce2' Hx'_key Hy'_key z) as Hunion_back.
          rewrite Hu in Hunion_back. cbn [snd equiv parent] in Hunion_back.
          specialize (Hunion_back Hz1).
          (* has_key z e2' -> has_key z e0 or in sub2' *)
          pose proof (rename_lookup_haskey_in y sub1' e1' z) as Hrl_y.
          rewrite Hry in Hrl_y. cbn [fst snd] in Hrl_y. specialize (Hrl_y Hunion_back).
          destruct Hrl_y as [Hz1' | Hex_y'].
          -- pose proof (rename_lookup_haskey_in x sub0 e0 z) as Hrl_x.
             rewrite Hrx in Hrl_x. cbn [fst snd] in Hrl_x. specialize (Hrl_x Hz1').
             destruct Hrl_x as [Hz0 | Hex_x''].
             ++ left. exact Hz0.
             ++ right. destruct Hex_x'' as [x'' Hlook''].
                exists x''.
                pose proof (rename_lookup_sub_mono y sub1' e1' x'' z Hlook'') as Hmono.
                rewrite Hry in Hmono. cbn [fst snd] in Hmono.
                (* Hmono : lookup sub2' x'' = Some z. Need: lookup sub_fin x'' = Some z. *)
                pose proof (clauses_to_instance_sub_mono cs sub2' e3' x'' z Hmono) as Hmono2.
                rewrite Hfin in Hmono2. cbn [fst snd] in Hmono2. exact Hmono2.
          -- right. destruct Hex_y' as [x'' Hlook']. exists x''.
             pose proof (clauses_to_instance_sub_mono cs sub2' e3' x'' z Hlook') as Hmono'.
             rewrite Hfin in Hmono'. cbn [fst snd] in Hmono'. exact Hmono'.
        * (* atom_clause *)
          unfold add_clause_to_instance in Hadd.
          cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind] in Hadd.
          cbn beta iota in Hadd. unfold Basics.compose in Hadd.
          destruct (rename_atom idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit
                      a_clause sub0 e0) as [p1 e1'] eqn:Hra. destruct p1 as [a' sub1'].
          cbn [fst snd uncurry] in Hadd.
          cbn [lift StateMonad.state_monad Mbind Mret fst snd] in Hadd.
          cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mseq Mbind Mret] in Hadd.
          cbn beta iota in Hadd. unfold Basics.compose in Hadd.
          destruct (update_entry a' e1') as [u' e2'] eqn:Hue. cbn [uncurry fst snd] in Hadd.
          injection Hadd as <- <- <-.
          (* Hz1 : has_key z e2' = snd(update_entry a' e1') *)
          assert (Hce1' : parent_closed e1').
          { pose proof (rename_atom_maintains_parent_closed a_clause sub0 e0 Hc) as H.
            rewrite Hra in H. cbn [snd] in H. exact H. }
          assert (Hsv1' : sub_values_keys sub1' e1').
          { pose proof (rename_atom_maintains_sub_values_keys a_clause sub0 e0 Hc Hsv) as H.
            rewrite Hra in H. cbn [fst snd] in H. exact H. }
          assert (Hdv1' : db_values_in_sub sub1' e1').
          { pose proof (rename_atom_maintains_db_values_in_sub a_clause sub0 e0 Hdv) as H.
            rewrite Hra in H. cbn [fst snd] in H. exact H. }
          assert (Hret_in_sub : exists x'', named_list_lookup_err sub1' x'' = Some (atom_ret a')).
          { exact (rename_atom_ret_in_sub a_clause sub0 e0 Hra). }
          assert (Hret_key : Sep.has_key (atom_ret a') (parent (equiv e1'))).
          { destruct Hret_in_sub as [x'' Hlook]. exact (Hsv1' x'' (atom_ret a') Hlook). }
          (* update_entry backward: has_key z e2' -> has_key z e1' *)
          assert (Hz1' : Sep.has_key z (parent (equiv e1'))).
          { (* Need update_entry_keys_in. For Some r branch, r is a key from db_values_in_sub. *)
            unfold update_entry in Hue. cbn [Mbind StateMonad.state_monad] in Hue.
            destruct (Defs.db_lookup idx symbol symbol_map idx_map idx_trie unit
                        (atom_fn a') (atom_args a') e1') as [mout e0'] eqn:Hlu.
            assert (He0' : e0' = e1').
            { unfold Defs.db_lookup in Hlu. cbn in Hlu. injection Hlu as _ <-. reflexivity. }
            subst e0'. destruct mout as [r|].
            - (* union r (atom_ret a') e1' *)
              cbn [Mseq Mbind Mret StateMonad.state_monad snd] in Hue.
              assert (Hr_key : Sep.has_key r (parent (equiv e1'))).
              { unfold Defs.db_lookup in Hlu. cbn in Hlu.
                destruct (map.get (db e1') (atom_fn a')) as [tbl|] eqn:Htbl; [|discriminate].
                cbn in Hlu.
                destruct (map.get tbl (atom_args a')) as [entry|] eqn:Hentry; [|discriminate].
                cbn in Hlu. injection Hlu as Hlu.
                specialize (Hdv1' (atom_fn a') tbl (atom_args a') entry Htbl Hentry) as [x'' Hlook'].
                rewrite <- Hlu. exact (Hsv1' x'' (entry_value idx unit entry) Hlook'). }
              pose proof (union_keys_in r (atom_ret a') e1' Hce1' Hr_key Hret_key z) as Huk.
              apply Huk.
              destruct (@Defs.union idx Eqb_idx symbol symbol_map idx_map idx_trie unit _ r (atom_ret a') e1') as [vv_r e_r] eqn:Hunion.
              cbn [snd]. cbn [snd] in Hue. injection Hue as _ He2'_eq. subst e2'. exact Hz1.
            - (* db_set: equiv unchanged *)
              (* Hue : db_set a' e1' = (u', e2'). db_set preserves equiv. *)
              unfold Defs.db_set in Hue. cbn [Mbind StateMonad.state_monad] in Hue.
              unfold Defs.get_analyses in Hue.
              destruct (list_Mmap (get_analysis idx symbol symbol_map idx_map idx_trie unit)
                                  (atom_args a') e1') as [pp e11] eqn:Hgg.
              cbn [fst snd] in Hue.
              destruct (Defs.update_analyses idx symbol symbol_map idx_map idx_trie unit
                          (atom_ret a') (analyze idx symbol unit a' pp) e11) as [pu e22] eqn:Huu.
              cbn [snd] in Hue. unfold db_set' in Hue. cbn [snd] in Hue.
              injection Hue as _ He2'_eq. rewrite <- He2'_eq in Hz1. cbn [equiv parent] in Hz1.
              unfold Defs.update_analyses in Huu. cbn [snd] in Huu. injection Huu as _ He22.
              rewrite <- He22 in Hz1. cbn [equiv parent] in Hz1.
              pose proof (list_Mmap_get_analysis_preserves_equiv_early (atom_args a') e1') as Heq1.
              rewrite Hgg in Heq1. cbn [snd] in Heq1. rewrite Heq1 in Hz1. exact Hz1. }
          (* now backward through rename_atom *)
          pose proof (rename_atom_haskey_in a_clause sub0 e0 z) as Hra_back.
          rewrite Hra in Hra_back. cbn [fst snd] in Hra_back. specialize (Hra_back Hz1').
          destruct Hra_back as [Hz0 | Hex_back].
          -- left. exact Hz0.
          -- right. destruct Hex_back as [x'' Hlook']. exists x''.
             pose proof (clauses_to_instance_sub_mono cs sub1' e2' x'' z Hlook') as Hmono_b.
             rewrite Hfin in Hmono_b. cbn [fst snd] in Hmono_b. exact Hmono_b.
      + right. destruct Hex' as [x' Hlook]. exists x'. exact Hlook.
  Qed.

  Lemma force_equiv_preserves_sound (m : model symbol)
    (i : idx_map (m.(domain symbol)))
    (e : instance) :
    (exists roots, union_find_ok lt (equiv e) roots) ->
    Semantics.egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie unit m i e ->
    Semantics.egraph_sound_for_interpretation idx symbol symbol_map idx_map idx_trie unit m i
      (snd (force_equiv idx Eqb_idx symbol symbol_map idx_map idx_trie (X:=unit) e)).
  Proof.
    intros Huf Hsnd.
    eapply Semantics.fields_preserved_sound_for_interpretation; [exact Hsnd|].
    pose proof (@force_equiv_sound idx Eqb_idx Eqb_idx_ok lt symbol symbol_map idx_map idx_map_ok idx_trie unit) as Hfe.
    unfold vc in Hfe.
    specialize (Hfe e).
    specialize (Hfe Huf).
    destruct Hfe as (Hdb & _ & Hper & Hpar & Hwl & Hkey).
    unfold Semantics.fields_preserved.
    repeat split.
    - symmetry. exact Hdb.
    - symmetry. exact Hpar.
    - cbn [force_equiv snd]. destruct e as [db' equiv' parents' epoch' wl' an' log']. cbn. reflexivity.
    - symmetry. exact Hwl.
    - cbn [force_equiv snd]. destruct e as [db' equiv' parents' epoch' wl' an' log']. cbn. reflexivity.
    - intro Hy. apply Hkey. exact Hy.
    - intro Hy. apply Hkey. exact Hy.
    - intro Hab. apply Hper. exact Hab.
    - intro Hab. apply Hper. exact Hab.
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
        /\ (forall a, In a atoms -> forall x, In x (atom_ret a :: atom_args a) ->
              exists y, named_list_lookup_err sub1 x = Some y)
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
    destruct Hinv1 as (_ & _ & Hwl1 & _ & Hfwd1 & Hvars1).
    split; [exact Hwl1 | exact (conj Hfwd1 Hvars1)].
  Qed.

  (* Helper: map f (flat_map g l) = flat_map (fun x => map f (g x)) l *)
  Lemma map_flat_map_dist {A B C} (f : B -> C) (g : A -> list B) (l : list A) :
    map f (flat_map g l) = flat_map (fun x => map f (g x)) l.
  Proof.
    induction l as [|a rest IH]; cbn.
    - reflexivity.
    - rewrite map_app. rewrite IH. reflexivity.
  Qed.

  (* Helper: NoDup of flat_map g l when elements of different g-images are
     disjoint by a tag function. *)
  Lemma NoDup_flat_map_by_tag {A B K} (tag : A -> K) (key : B -> K) (g : A -> list B) (l : list A) :
    NoDup (map tag l) ->
    (forall x, In x l -> NoDup (g x)) ->
    (forall x b, In x l -> In b (g x) -> key b = tag x) ->
    NoDup (flat_map g l).
  Proof.
    induction l as [|a rest IH]; intros Htag Hinner Hkey; cbn.
    - constructor.
    - inversion Htag as [|? ? Hnotin Hrest]; subst.
      rewrite NoDup_app_iff. repeat split.
      + apply Hinner. left. reflexivity.
      + apply IH.
        * exact Hrest.
        * intros x Hx. apply Hinner. right. exact Hx.
        * intros x b Hx Hbx. exact (Hkey x b (or_intror Hx) Hbx).
      + intros b Hb1 Hb2.
        apply in_flat_map in Hb2.
        destruct Hb2 as (x & Hx & Hbx).
        apply Hnotin.
        pose proof (Hkey a b (or_introl eq_refl) Hb1) as Hka.
        pose proof (Hkey x b (or_intror Hx) Hbx) as Hkx.
        rewrite <- Hka. rewrite Hkx.
        apply in_map. exact Hx.
      + intros b Hb1 Hb2.
        apply in_flat_map in Hb1.
        destruct Hb1 as (x & Hx & Hbx).
        apply Hnotin.
        pose proof (Hkey a b (or_introl eq_refl) Hb2) as Hka.
        pose proof (Hkey x b (or_intror Hx) Hbx) as Hkx.
        rewrite <- Hka. rewrite Hkx.
        apply in_map. exact Hx.
  Qed.

  (* The (atom_fn, atom_args) pairs of db_to_atoms are unique because they
     correspond to the nested map keys of the db, which are unique. *)
  Lemma db_to_atoms_NoDup_fn_args (d : db_map idx symbol symbol_map idx_trie unit) :
    NoDup (map (fun a => (atom_fn a, atom_args a)) (db_to_atoms d)).
  Proof.
    unfold db_to_atoms, Semantics.db_to_atoms.
    rewrite map_flat_map_dist.
    apply NoDup_flat_map_by_tag with (tag := fst) (key := fst).
    - apply FinFun.Injective_map_NoDup_in.
      + intros (s1, t1) (s2, t2) H1 H2 Heq. cbn in Heq. subst s2.
        apply Properties.map.tuples_spec in H1.
        apply Properties.map.tuples_spec in H2.
        congruence.
      + apply Properties.map.tuples_NoDup.
    - intros (f, tbl) Hft.
      unfold table_atoms, Semantics.table_atoms. cbn.
      apply FinFun.Injective_map_NoDup_in.
      + intros a1 a2 Ha1 Ha2 Heq.
        apply in_map_iff in Ha1. destruct Ha1 as ((k1, e1) & Hrta1 & Hk1).
        apply in_map_iff in Ha2. destruct Ha2 as ((k2, e2) & Hrta2 & Hk2).
        unfold row_to_atom, Semantics.row_to_atom in Hrta1, Hrta2.
        subst a1 a2. cbn in Heq. injection Heq. intros Hargs. subst k2.
        apply Properties.map.tuples_spec in Hk1.
        apply Properties.map.tuples_spec in Hk2.
        congruence.
      + apply FinFun.Injective_map_NoDup_in.
        * intros (k1, e1) (k2, e2) Hk1 Hk2 Heq. injection Heq. intros _ Hk. subst k1.
          apply Properties.map.tuples_spec in Hk1.
          apply Properties.map.tuples_spec in Hk2.
          congruence.
        * apply Properties.map.tuples_NoDup.
    - intros (f, tbl) (fn_sym, args_k) Hft Hfnk.
      unfold table_atoms, Semantics.table_atoms in Hfnk. cbn in Hfnk.
      rewrite in_map_iff in Hfnk.
      destruct Hfnk as (a & Heq & Ha).
      apply in_map_iff in Ha.
      destruct Ha as ((k, e) & Hrta & Hke).
      unfold row_to_atom, Semantics.row_to_atom in Hrta.
      subst a. cbn in Heq. injection Heq. intros _ Hfn. subst fn_sym. cbn. reflexivity.
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
  (* Bridge (iii): compile_rule_inl_erule_sound                      *)
  (* ============================================================== *)

  (* Helper: restrict an assignment to a list of keys *)
  Definition restrict_assignment {A} (qv : list idx) (a : idx_map A) : idx_map A :=
    map.fold (fun acc k v => if inb k qv then map.put acc k v else acc) map.empty a.

  Lemma get_restrict_assignment {A} (qv : list idx) (a : idx_map A) (x : idx) :
    map.get (restrict_assignment qv a) x = if inb x qv then map.get a x else None.
  Proof.
    unfold restrict_assignment.
    eapply (@map.fold_spec idx A (idx_map A) (idx_map_ok A)
      (idx_map A)
      (fun m acc => map.get acc x = if inb x qv then map.get m x else None)
      (fun acc k v => if inb k qv then map.put acc k v else acc)
      map.empty).
    - rewrite !map.get_empty. destruct (inb x qv); reflexivity.
    - intros k v m acc Hnotk IH.
      destruct (inb k qv) eqn:Hkq; destruct (eqb x k) eqn:Hxk.
      + pose proof (@eqb_spec idx Eqb_idx Eqb_idx_ok x k) as Hbs.
        rewrite Hxk in Hbs. subst k.
        rewrite !map.get_put_same. rewrite Hkq. reflexivity.
      + pose proof (@eqb_spec idx Eqb_idx Eqb_idx_ok x k) as Hbs.
        rewrite Hxk in Hbs.
        rewrite !map.get_put_diff by exact Hbs.
        exact IH.
      + pose proof (@eqb_spec idx Eqb_idx Eqb_idx_ok x k) as Hbs.
        rewrite Hxk in Hbs. subst k.
        rewrite map.get_put_same.
        rewrite Hkq in IH. rewrite Hkq. exact IH.
      + pose proof (@eqb_spec idx Eqb_idx Eqb_idx_ok x k) as Hbs.
        rewrite Hxk in Hbs.
        rewrite map.get_put_diff by exact Hbs.
        exact IH.
  Qed.

  (* list_Mmap congruence under pointwise agreement *)
  Lemma list_Mmap_get_agree' {D} (a1 a2 : idx_map D) (xs : list idx) :
    (forall x, In x xs -> map.get a1 x = map.get a2 x) ->
    list_Mmap (map.get a1) xs = list_Mmap (map.get a2) xs.
  Proof.
    intros Hagree.
    induction xs as [|x xs IH]; cbn.
    - reflexivity.
    - rewrite (Hagree x (or_introl eq_refl)).
      destruct (map.get a2 x) as [v|]; cbn.
      + rewrite (IH (fun z Hz => Hagree z (or_intror Hz))). reflexivity.
      + reflexivity.
  Qed.

  (* Soundness agree lemmas: recast soundness under pointwise agreement *)
  Lemma atom_sound_for_model_agree (m : model symbol) (a1 a2 : idx_map m.(Semantics.domain symbol))
      (at_ : atom) :
    (forall x, In x (at_.(atom_ret) :: at_.(atom_args)) -> map.get a1 x = map.get a2 x) ->
    Semantics.atom_sound_for_model idx symbol idx_map m a1 at_ ->
    Semantics.atom_sound_for_model idx symbol idx_map m a2 at_.
  Proof.
    intros Hagree Hsnd.
    unfold Semantics.atom_sound_for_model in *.
    destruct (list_Mmap (map.get a1) at_.(atom_args)) as [args|] eqn:Hargs.
    - destruct (map.get a1 at_.(atom_ret)) as [out|] eqn:Hret; cbn in Hsnd.
      + rewrite (list_Mmap_get_agree' a1 a2 _ (fun z Hz => Hagree z (or_intror Hz))) in Hargs.
        rewrite Hargs. cbn [Is_Some_satisfying].
        rewrite <- (Hagree _ (or_introl eq_refl)). rewrite Hret.
        cbn [Is_Some_satisfying]. exact Hsnd.
      + contradiction.
    - contradiction.
  Qed.

  Lemma eq_sound_for_model_agree (m : model symbol) (a1 a2 : idx_map m.(Semantics.domain symbol))
      (x y : idx) :
    map.get a1 x = map.get a2 x -> map.get a1 y = map.get a2 y ->
    Semantics.eq_sound_for_model idx symbol idx_map m a1 x y ->
    Semantics.eq_sound_for_model idx symbol idx_map m a2 x y.
  Proof.
    intros Hx Hy Hsnd.
    unfold Semantics.eq_sound_for_model in *.
    destruct (map.get a1 x) as [vx|] eqn:Hgx; cbn in Hsnd; [| contradiction].
    destruct (map.get a1 y) as [vy|] eqn:Hgy; cbn in Hsnd; [| contradiction].
    rewrite <- Hx. rewrite <- Hy. cbn [Is_Some_satisfying]. exact Hsnd.
  Qed.

  Lemma clause_sound_for_model_agree (m : model symbol) (a1 a2 : idx_map m.(Semantics.domain symbol))
      (c : clause) :
    (forall x, In x (Semantics.clause_vars idx symbol c) -> map.get a1 x = map.get a2 x) ->
    Semantics.clause_sound_for_model idx symbol idx_map m a1 c ->
    Semantics.clause_sound_for_model idx symbol idx_map m a2 c.
  Proof.
    intros Hagree Hsnd.
    destruct c as [x y | at_]; cbn [Semantics.clause_sound_for_model Semantics.clause_vars] in *.
    - eapply eq_sound_for_model_agree.
      + apply Hagree. left. reflexivity.
      + apply Hagree. right. left. reflexivity.
      + exact Hsnd.
    - eapply atom_sound_for_model_agree.
      + intros z Hz. apply Hagree. exact Hz.
      + exact Hsnd.
  Qed.

  Lemma all_clause_sound_for_model_agree (m : model symbol) (a1 a2 : idx_map m.(Semantics.domain symbol))
      (cs : list clause) :
    (forall x, In x (flat_map (Semantics.clause_vars idx symbol) cs) -> map.get a1 x = map.get a2 x) ->
    all (Semantics.clause_sound_for_model idx symbol idx_map m a1) cs ->
    all (Semantics.clause_sound_for_model idx symbol idx_map m a2) cs.
  Proof.
    intros Hagree.
    induction cs as [| c cs IH]; cbn; intros H; [exact H|].
    destruct H as [Hc Hcs].
    split.
    - eapply clause_sound_for_model_agree.
      + intros x Hx. apply Hagree. apply in_or_app. left. exact Hx.
      + exact Hc.
    - apply IH.
      + intros x Hx. apply Hagree. apply in_or_app. right. exact Hx.
      + exact Hcs.
  Qed.

  (* Helper: every var of a sound clause has a wf domain value *)
  Lemma clause_sound_for_model_wf_var (m : model symbol) (Hm : Semantics.model_ok symbol m)
      (a : idx_map m.(Semantics.domain symbol)) (c : clause) (x : idx) :
    In x (Semantics.clause_vars idx symbol c) ->
    Semantics.clause_sound_for_model idx symbol idx_map m a c ->
    exists d, map.get a x = Some d /\ m.(Semantics.domain_wf symbol) d.
  Proof.
    intros Hx Hsnd.
    destruct c as [u v | at_].
    - cbn [Semantics.clause_vars] in Hx.
      unfold Semantics.clause_sound_for_model, Semantics.eq_sound_for_model in Hsnd.
      destruct (map.get a u) as [vu|] eqn:Hgu; cbn [Is_Some_satisfying] in Hsnd.
      2: exact (False_ind _ Hsnd).
      destruct (map.get a v) as [vv|] eqn:Hgv; cbn [Is_Some_satisfying] in Hsnd.
      2: exact (False_ind _ Hsnd).
      cbn [In] in Hx.
      destruct Hx as [ Hxu | [ Hxv | Hfalse ] ].
      + subst x. exists vu. split; [exact Hgu|].
        unfold Semantics.domain_wf. transitivity vv; [exact Hsnd | symmetry; exact Hsnd].
      + subst x. exists vv. split; [exact Hgv|].
        unfold Semantics.domain_wf. transitivity vu; [symmetry; exact Hsnd | exact Hsnd].
      + destruct Hfalse.
    - cbn [Semantics.clause_vars] in Hx.
      unfold Semantics.clause_sound_for_model, Semantics.atom_sound_for_model in Hsnd.
      destruct (list_Mmap (map.get a) at_.(atom_args)) as [args|] eqn:Hargs;
        cbn [Is_Some_satisfying] in Hsnd. 2: exact (False_ind _ Hsnd).
      destruct (map.get a at_.(atom_ret)) as [out|] eqn:Hret;
        cbn [Is_Some_satisfying] in Hsnd. 2: exact (False_ind _ Hsnd).
      destruct Hx as [ Hxret | Hxarg ].
      + subst x. exists out. split; [exact Hret|].
        eapply Semantics.interprets_to_implies_wf_conclusion; [exact Hm | exact Hsnd].
      + assert (Harg_vals : exists vx, map.get a x = Some vx /\ In vx args).
        * clear out Hret Hsnd.
          revert x args Hxarg Hargs.
          induction at_.(atom_args) as [ | a0 rest IH2]; intros x args Hx Hm2.
          -- destruct Hx.
          -- cbn in Hm2.
             destruct (map.get a a0) as [va0|] eqn:Ha0; cbn in Hm2; [| discriminate].
             destruct (list_Mmap (map.get a) rest) as [vrest|] eqn:Hrest; cbn in Hm2; [| discriminate].
             inversion Hm2; subst args.
             destruct Hx as [ Hxa0 | Hxrest ].
             ++ subst x. exists va0. split; [exact Ha0 | left; reflexivity].
             ++ destruct (IH2 x vrest Hxrest eq_refl) as [ vx [ Hvx Hin ] ].
                exists vx. split; [exact Hvx | right; exact Hin].
        * destruct Harg_vals as [ vx [ Hvx Hinvx ] ].
          exists vx. split; [exact Hvx|].
          pose proof (@Semantics.interprets_to_implies_wf_args symbol m Hm (atom_fn at_) args out Hsnd) as Hall.
          exact (in_all _ _ _ Hall Hinvx).
  Qed.

  (* Bridge: the compiled-rule's sequent fields equal those of optimize_sequent at matching fuel *)
  Lemma optimize_sequent_fields :
    forall r,
      let fuel := (let var_count :=
            length (flat_map (Semantics.clause_vars idx symbol) r.(Semantics.seq_assumptions)
                    ++ flat_map (Semantics.clause_vars idx symbol) r.(Semantics.seq_conclusions))
          in var_count * var_count) in
      let '(assumptions, catoms, ceqs) :=
        QueryOpt.optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie r fuel in
      (optimize_sequent r).(Semantics.seq_assumptions) = map (@atom_clause idx symbol) assumptions /\
      (optimize_sequent r).(Semantics.seq_conclusions) =
        map (uncurry (@eq_clause idx symbol)) ceqs ++ map (@atom_clause idx symbol) catoms.
  Proof.
    intros r.
    unfold QueryOpt.optimize_sequent', QueryOpt.sequent'_of_states.
    cbn. split; reflexivity.
  Qed.

  (* KEYSTONE: compile_rule_inl_erule_sound
     Connects model_satisfies_rule (on the optimizer's sequent) to erule_sound
     (the saturation engine's per-rule soundness).

     Hypotheses:
     - Halign_assum: map atom_clause (query_atoms qc er) = seq_assumptions (optimize_sequent r)
       (bridges the qc-pointer reconstruction to the optimizer's atom list)
     - Halign_concl: seq_conclusions (optimize_sequent r) = write_unifs ++ write_clauses
       (bridges the optimizer's conclusion list to er's write fields; follows from
        optimize_sequent_fields when rf = var_count^2)
     - Hvars_eq: the forall_vars of (optimize_sequent r) coincide with query_vars er
       (needed to show the restriction a_c has the right domain) *)
  Lemma compile_rule_inl_erule_sound :
    forall rf r st0 er st1 (m : model symbol) (Hm : Semantics.model_ok symbol m)
           (qc : symbol_map (idx_map (list nat * nat))) (sopt : sequent),
      compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf r st0
        = (inl er, st1) ->
      (* Assumption alignment: query_atoms of er = seq_assumptions of the optimized sequent.
         [sopt] is abstract (any sequent satisfying the alignment) so this keystone is
         independent of the optimize fuel; the consumer instantiates [sopt] at the
         optimize_sequent of [r] at the same fuel [compile_rule] used. *)
      map (@atom_clause idx symbol)
          (Semantics.query_atoms idx idx_zero symbol symbol_map idx_map qc er)
        = sopt.(Semantics.seq_assumptions) ->
      (* Conclusion alignment: seq_conclusions of sopt = er's write fields *)
      sopt.(Semantics.seq_conclusions) =
        map (uncurry (@eq_clause idx symbol)) (write_unifications idx symbol er)
        ++ map (@atom_clause idx symbol) (write_clauses idx symbol er) ->
      (* Variable alignment: forall_vars ↔ query_vars *)
      (forall x, In x (Semantics.forall_vars sopt) <->
                 In x (query_vars idx symbol er)) ->
      model_satisfies_rule m sopt ->
      Semantics.erule_sound idx idx_zero symbol symbol_map idx_map m qc er.
  Proof.
    intros rf r st0 er st1 m Hm qc sopt Hc Halign_assum Halign_concl Hvars_eq Hmsr.
    (* Step 1: destruct compile_rule to learn er's fields *)
    unfold compile_rule in Hc.
    destruct (QueryOpt.optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map
                idx_map idx_trie r rf)
      as [ [assumptions catoms] ceqs ] eqn:Hopt.
    set (qvs := dedup (eqb (A:=idx)) (flat_map (atom_fvs idx symbol) assumptions)) in *.
    set (cvars := clauses_fvs idx Eqb_idx symbol
      (map (uncurry (@eq_clause idx symbol)) ceqs ++ map (@atom_clause idx symbol) catoms) qvs) in *.
    destruct (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map
                           idx_map qvs) assumptions st0)
      as [qcls_ptrs st'] eqn:Hmap.
    cbn [Mbind StateMonad.state_monad] in Hc.
    rewrite Hmap in Hc.
    destruct qcls_ptrs as [| c cs].
    - cbn [Mret StateMonad.state_monad] in Hc. inversion Hc.
    - cbn [Mret StateMonad.state_monad] in Hc. inversion Hc.
      subst st1.
      (* H0 : Build_erule ... = er *)
      subst er.
      (* Now: query_vars er = qvs, write_clauses er = catoms, write_unifications er = ceqs *)
      cbn [query_vars write_clauses write_unifications write_vars] in *.
      (* Step 2: unfold erule_sound and introduce a_q *)
      unfold Semantics.erule_sound.
      intros a_q Hwf_q Hsnd_q.
      (* Step 3: define a_c = restrict a_q to qvs *)
      set (a_c := restrict_assignment qvs a_q).
      (* Step 4a: convert atom_sound a_q to clause_sound a_q on seq_assumptions *)
      (* Build all (clause_sound a_q) (map atom_clause (query_atoms qc er)) from Hsnd_q *)
      pose proof (all_map_in (@atom_clause idx symbol)
                    (Semantics.clause_sound_for_model idx symbol idx_map m a_q)
                    (query_atoms idx idx_zero symbol symbol_map idx_map qc
                       {| query_vars := qvs; query_clause_ptrs := (c, cs);
                          write_vars := cvars; write_clauses := catoms;
                          write_unifications := ceqs |})
                    (fun at_ Hat_ => in_all _ _ _ Hsnd_q Hat_)) as Hcsnd_map.
      rewrite Halign_assum in Hcsnd_map.
      rename Hcsnd_map into Hcsnd_aq.
      (* Step 4b: a_c agrees with a_q on forall_vars *)
      assert (Hagree : forall x, In x (forall_vars sopt) ->
                map.get a_q x = map.get a_c x);
        [ intros x Hx;
          unfold a_c; rewrite get_restrict_assignment;
          assert (Hin_qvs : In x qvs) by exact (proj1 (Hvars_eq x) Hx);
          apply (proj2 (@inb_is_In idx Eqb_idx Eqb_idx_ok x qvs)) in Hin_qvs;
          destruct (inb x qvs); [reflexivity | exact (False_ind _ Hin_qvs)]
        | idtac ].
      (* Step 4c: clause_sound a_c on seq_assumptions *)
      pose proof (all_clause_sound_for_model_agree m a_q a_c
                    (seq_assumptions sopt)
                    (fun x Hx => Hagree x Hx)
                    Hcsnd_aq) as Hcsnd_ac.
      (* Step 4d: confinement — every key of a_c is in forall_vars *)
      assert (Hconf : forall x, Sep.has_key x a_c -> In x (forall_vars sopt));
        [ intros x Hkey;
          unfold Sep.has_key in Hkey; unfold a_c in Hkey;
          rewrite get_restrict_assignment in Hkey;
          destruct (inb x qvs) eqn:Hinb;
          [ apply (proj2 (Hvars_eq x));
            apply (@inb_is_In idx Eqb_idx Eqb_idx_ok x qvs); rewrite Hinb; exact I
          | exact (False_ind _ Hkey) ]
        | idtac ].
      (* Step 4e: coverage — every forall_var is a key of a_c *)
      assert (Hcov : forall x, In x (forall_vars sopt) -> Sep.has_key x a_c);
        [ intros x Hx;
          unfold Sep.has_key, a_c; rewrite get_restrict_assignment;
          assert (Hin_qvs : In x qvs) by exact (proj1 (Hvars_eq x) Hx);
          assert (Htrue : Is_true (inb x qvs)) by (apply (@inb_is_In idx Eqb_idx Eqb_idx_ok); exact Hin_qvs);
          destruct (inb x qvs) eqn:Hinb;
          [ destruct (Hwf_q x (proj1 (Hvars_eq x) Hx)) as [ d Hd ];
            destruct Hd as [ Hd1 _ ];
            rewrite Hd1; exact I
          | exact (False_ind _ Htrue) ]
        | idtac ].
      (* Step 5: apply model_satisfies_rule to get a' *)
      destruct (Hmsr a_c Hcov Hconf Hcsnd_ac) as [ a' Hext_ccl ].
      destruct Hext_ccl as [ Hext Hccl ].
      exists a'.
      cbn [write_clauses write_unifications write_vars query_vars].
      (* Extract Hccl_eqs and Hccl_atoms from Hccl *)
      pose proof Hccl as Hccl_full.
      rewrite Halign_concl in Hccl_full.
      rewrite all_app in Hccl_full.
      destruct Hccl_full as [ Hccl_eqs Hccl_atoms ].
      split.
      { (* query_vars: get a' x = get a_q x for x in qvs *)
        intros x Hx_qvs.
        assert (Hac_eq : map.get a_c x = map.get a_q x);
          [ unfold a_c; rewrite get_restrict_assignment;
            assert (Htrue : Is_true (inb x qvs)) by (apply (@inb_is_In idx Eqb_idx Eqb_idx_ok); exact Hx_qvs);
            destruct (inb x qvs); [reflexivity | exact (False_ind _ Htrue)]
          | idtac ].
        destruct (Hwf_q x Hx_qvs) as [ d Hd ].
        destruct Hd as [ Hd1 _ ].
        rewrite <- Hac_eq in Hd1.
        rewrite (Hext _ _ Hd1). congruence. }
      split.
      { (* write_vars: use clause_sound_for_model_wf_var for both ceqs and catoms *)
        intros x Hx_wv.
        unfold cvars in Hx_wv. unfold clauses_fvs in Hx_wv.
        apply filter_In in Hx_wv as [ Hx_flat Hbool ].
        apply (proj2 (@dedup_preserves_In idx eqb (@eqb_boolspec idx Eqb_idx Eqb_idx_ok) _ x)) in Hx_flat.
        rewrite flat_map_app in Hx_flat.
        apply in_app_iff in Hx_flat as [ Hx_eqs | Hx_atoms ].
        * apply in_flat_map in Hx_eqs as [ cl [ Hin_cl Hx_cl ] ].
          apply in_map_iff in Hin_cl as [ p [ Hcleq Hin_p ] ].
          subst cl.
          pose proof (in_all _ _ _ Hccl_eqs (in_map _ _ _ Hin_p)) as Hcl_snd.
          exact (clause_sound_for_model_wf_var m Hm a' (uncurry eq_clause p) x Hx_cl Hcl_snd).
        * apply in_flat_map in Hx_atoms as [ cl [ Hin_cl Hx_cl ] ].
          apply in_map_iff in Hin_cl as [ at_ [ Hcleq Hin_at ] ].
          subst cl.
          pose proof (in_all _ _ _ Hccl_atoms (in_map _ _ _ Hin_at)) as Hcl_snd.
          exact (clause_sound_for_model_wf_var m Hm a' (atom_clause at_) x Hx_cl Hcl_snd). }
      split.
      { (* write_clauses: all atom_sound a' catoms *)
        apply all_wkn with (P := fun at_ => Semantics.clause_sound_for_model idx symbol idx_map m a' (atom_clause at_)).
        - intros at_ _ Hc_. exact Hc_.
        - rewrite <- all_map. exact Hccl_atoms. }
      { (* write_unifications: all eq_sound a' ceqs *)
        apply all_wkn with (P := fun p => Semantics.clause_sound_for_model idx symbol idx_map m a' (uncurry (@eq_clause idx symbol) p)).
        - intros uv _ Hc_.
          destruct uv as [u v].
          cbn [uncurry Semantics.clause_sound_for_model Semantics.eq_sound_for_model] in Hc_.
          cbn [fst snd Semantics.eq_sound_for_model].
          exact Hc_.
        - rewrite <- all_map. exact Hccl_eqs. }
  Qed.

  (* Helper: named_list_lookup result is independent of the default
     when the key is present in the list (assuming enough values). *)
  Lemma named_list_lookup_default_indep :
    forall {B : Type} (qs : list idx) (vs : list B) (k : idx) (d1 d2 : B),
      NoDup qs -> In k qs -> List.length qs <= List.length vs ->
      named_list_lookup d1 (combine qs vs) k = named_list_lookup d2 (combine qs vs) k.
  Proof.
    induction qs as [| q qs' IH]; intros vs k d1 d2 HND HIn Hlen.
    - inversion HIn.
    - destruct vs as [| v vs'].
      + cbn [List.length] in Hlen. Lia.lia.
      + cbn [combine named_list_lookup].
        destruct (eqb k q) eqn:Heq.
        * reflexivity.
        * inversion HND as [ | ? ? Hna HND']; subst.
          assert (HIn' : In k qs'). {
            destruct HIn as [-> | HIn'].
            - rewrite eqb_refl_true in Heq; [ discriminate | exact Eqb_idx_ok].
            - exact HIn'. }
          cbn [List.length] in Hlen.
          apply IH; [ exact HND' | exact HIn' | Lia.lia ].
  Qed.

  (* Helper: the lookup of x in (combine l (seq base (length l)))
     returns base + position-of-x-in-l, given NoDup and a witness. *)
  Lemma named_list_lookup_combine_seq_position :
    forall (l : list idx) (x : idx) (base n : nat),
      NoDup l ->
      nth_error l n = Some x ->
      named_list_lookup base (combine l (seq base (List.length l))) x = base + n.
  Proof.
    induction l as [| a l' IH]; intros x base n HND Hnth.
    - destruct n; discriminate.
    - cbn [List.length seq combine named_list_lookup].
      destruct n as [| n'].
      + cbn [nth_error] in Hnth. injection Hnth; intro Heq; subst a.
        rewrite eqb_refl_true; [ | exact Eqb_idx_ok]. Lia.lia.
      + cbn [nth_error] in Hnth.
        inversion HND as [ | ? ? H_notin H_nd' ]; subst.
        assert (Hneq : eqb x a = false). {
          apply eqb_ineq_false; [ exact Eqb_idx_ok | ].
          left. intro Hxa. subst x.
          exact (H_notin (nth_error_In _ _ Hnth)). }
        rewrite Hneq.
        specialize (IH x (S base) n' H_nd' Hnth).
        assert (Hdi : named_list_lookup base (combine l' (seq (S base) (Datatypes.length l'))) x
                    = named_list_lookup (S base) (combine l' (seq (S base) (Datatypes.length l'))) x). {
          apply named_list_lookup_default_indep; [ exact H_nd' | apply nth_error_In in Hnth; exact Hnth | ].
          rewrite List.seq_length. Lia.lia. }
        Lia.lia.
  Qed.

  (* Lemma 1: round-trip for a single element.
     named_list_lookup 0 (combine l (seq 0 n)) x gives the position k of x in l,
     and nth k l = x. *)
  Lemma nth_named_list_lookup_combine_seq :
    forall (l : list idx) (x : idx),
      NoDup l -> In x l ->
      nth (named_list_lookup 0 (combine l (seq 0 (List.length l))) x) l idx_zero = x.
  Proof.
    intros l x HND HIn.
    pose proof (In_nth_error l x HIn) as [n Hnth_err].
    assert (Hpos : named_list_lookup 0 (combine l (seq 0 (List.length l))) x = n). {
      pose proof (named_list_lookup_combine_seq_position l x 0 n HND Hnth_err).
      Lia.lia. }
    rewrite Hpos.
    apply nth_error_nth with (x := x).
    exact Hnth_err.
  Qed.

  (* Lemma 2: map corollary — applying the round-trip pointwise. *)
  Lemma map_nth_named_list_lookup_combine_seq :
    forall (l : list idx) (args : list idx),
      NoDup l -> (forall x, In x args -> In x l) ->
      map (fun k => nth k l idx_zero)
          (map (named_list_lookup 0 (combine l (seq 0 (List.length l)))) args) = args.
  Proof.
    intros l args HND Hargs.
    rewrite List.map_map.
    apply map_ext_id.
    intros x HIn.
    pose proof (In_nth_error l x (Hargs x HIn)) as [n Hn].
    assert (Hpos : named_list_lookup 0 (combine l (seq 0 (List.length l))) x = n). {
      pose proof (named_list_lookup_combine_seq_position l x 0 n HND Hn).
      Lia.lia. }
    rewrite Hpos.
    apply nth_error_nth with (x := x).
    exact Hn.
  Qed.

  (* Lemma 3: map_inverse_get correctness —
     if map_inverse_get m v = Some i, then map.get m i = Some v. *)
  Lemma map_inverse_get_correct :
    forall {value} {Eqb_v : Eqb value} (Hok_v : Eqb_ok Eqb_v)
           (m : idx_map value) (v : value) (i : idx),
      QueryOpt.map_inverse_get m v = Some i -> map.get m i = Some v.
  Proof.
    intros value Eqb_v Hok_v m v i Hinv.
    unfold QueryOpt.map_inverse_get in Hinv.
    revert Hinv.
    apply (@map.fold_spec idx value (idx_map value) (idx_map_ok value)
        (option idx)
        (fun m' r => r = Some i -> map.get m' i = Some v)).
    - intro H. discriminate H.
    - intros k v' m' r Hget IH Hfold.
      destruct (eqb v v') eqn:Heqv.
      + injection Hfold; intro Heqi; subst k.
        rewrite map.get_put_same.
        f_equal.
        pose proof (@eqb_spec value Eqb_v Hok_v v v') as Hspec.
        rewrite Heqv in Hspec. exact (eq_sym Hspec).
      + apply IH in Hfold.
        destruct (eqb i k) eqn:Hik.
        * pose proof (@eqb_spec idx Eqb_idx Eqb_idx_ok i k) as Hspec.
          rewrite Hik in Hspec. subst k.
          rewrite Hget in Hfold. discriminate.
        * rewrite map.get_put_diff; [ exact Hfold | ].
          pose proof (@eqb_spec idx Eqb_idx Eqb_idx_ok i k) as Hspec.
          rewrite Hik in Hspec. exact Hspec.
  Qed.

  (* ============================================================== *)
  (* qc_entry / wf_qc_state: hash_clause soundness + monotonicity   *)
  (* ============================================================== *)

  Definition St := symbol_map (idx * idx_map (list nat * nat)).

  Definition qc_entry (S : St) (f : symbol) (i : idx) (v : list nat * nat) : Prop :=
    exists last m, map.get S f = Some (last, m) /\ map.get m i = Some v.

  Definition wf_qc_state (S : St) : Prop :=
    forall f last m, map.get S f = Some (last, m) ->
      forall k, map.get m k <> None -> lt k (idx_succ last).

  Lemma wf_qc_state_empty : wf_qc_state map.empty.
  Proof.
    unfold wf_qc_state.
    intros f last m Hget.
    pose proof (@map.get_empty symbol (idx * idx_map (list nat * nat)) (symbol_map _) (symbol_map_ok _) f) as Hempty.
    change St with (symbol_map (idx * idx_map (list nat * nat))) in Hget.
    rewrite Hempty in Hget. discriminate Hget.
  Qed.

  Lemma hash_clause_sets : forall (a : Defs.atom nat symbol) (S : St),
    qc_entry (snd (hash_clause idx idx_succ idx_zero symbol symbol_map idx_map a S))
             (Defs.atom_fn a)
             (fst (hash_clause idx idx_succ idx_zero symbol symbol_map idx_map a S))
             (Defs.atom_args a, Defs.atom_ret a).
  Proof.
    intros [f args out] S.
    unfold qc_entry.
    cbn [Defs.atom_fn Defs.atom_args Defs.atom_ret].
    destruct (hash_clause idx idx_succ idx_zero symbol symbol_map idx_map
                {| atom_fn := f; atom_args := args; atom_ret := out |} S)
      as [i S'] eqn:Hhc.
    cbn [fst snd].
    unfold hash_clause in Hhc. cbn in Hhc.
    change St with (symbol_map (idx * idx_map (list nat * nat))) in *.
    destruct (map.get S f) as [ [last m] | ] eqn:HgetSf.
    - destruct (map_inverse_get m (args, out)) as [j|] eqn:Hinv.
      + (* REUSE: Hhc : (j, S) = (i, S') *)
        injection Hhc; intros HS Hi; subst S' j.
        exists last, m. split.
        * exact HgetSf.
        * exact (map_inverse_get_correct _ m (args, out) i Hinv).
      + (* NEW_ID: Hhc : (idx_succ last, map.put S f ...) = (i, S') *)
        injection Hhc; intros HS Hi; subst S' i.
        exists (idx_succ last), (map.put m (idx_succ last) (args, out)). split.
        * apply (@map.get_put_same symbol _ _ (symbol_map_ok _)).
        * apply (@map.get_put_same idx _ _ (idx_map_ok _)).
    - (* None: Hhc : (idx_zero, map.put S f ...) = (i, S') *)
      injection Hhc; intros HS Hi; subst S' i.
      exists (@default idx idx_zero), (map.singleton idx_zero (args, out)). split.
      * apply (@map.get_put_same symbol _ _ (symbol_map_ok _)).
      * unfold map.singleton. apply (@map.get_put_same idx _ _ (idx_map_ok _)).
  Qed.

  Lemma hash_clause_preserves_wf (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt) :
    forall (a : Defs.atom nat symbol) (S : St),
      wf_qc_state S -> wf_qc_state (snd (hash_clause idx idx_succ idx_zero symbol symbol_map idx_map a S)).
  Proof.
    intros [f args out] S Hwf.
    unfold hash_clause.
    change St with (symbol_map (idx * idx_map (list nat * nat))) in *.
    cbn [fst snd].
    destruct (map.get S f) as [ [last m] | ] eqn:HgetSf.
    - destruct (map_inverse_get m (args, out)) as [j|] eqn:Hinv.
      + exact Hwf.
      + unfold wf_qc_state in *.
        intros g last' m' HgetS'g k Hk.
        cbn [fst snd] in HgetS'g.
        destruct (eqb g f) eqn:Hgf.
        ++ pose proof (@eqb_spec symbol Eqb_symbol Eqb_symbol_ok g f) as Hspec.
           rewrite Hgf in Hspec. subst g.
           assert (Hgps := @map.get_put_same symbol _ (symbol_map _) (symbol_map_ok _)
                             S f (idx_succ last, map.put m (idx_succ last) (args, out))).
           assert (Heq := eq_trans (eq_sym Hgps) HgetS'g).
           injection Heq; intros Hm' Hlast'; subst last' m'.
           destruct (eqb k (idx_succ last)) eqn:Hklast.
           +++ pose proof (@eqb_spec idx Eqb_idx Eqb_idx_ok k (idx_succ last)) as Hkspec.
               rewrite Hklast in Hkspec. subst k. apply Hlts.
           +++ pose proof (@eqb_spec idx Eqb_idx Eqb_idx_ok k (idx_succ last)) as Hkspec.
               rewrite Hklast in Hkspec.
               assert (Hkd := @map.get_put_diff idx (list nat * nat) (idx_map _) (idx_map_ok _)
                                m k (args,out) (idx_succ last) Hkspec).
               rewrite Hkd in Hk.
               exact (Hltt _ _ _ (Hwf f last m HgetSf k Hk) (Hlts (idx_succ last))).
        ++ pose proof (@eqb_spec symbol Eqb_symbol Eqb_symbol_ok g f) as Hspec.
           rewrite Hgf in Hspec.
           assert (Hgd := @map.get_put_diff symbol _ (symbol_map _) (symbol_map_ok _)
                            S g (idx_succ last, map.put m (idx_succ last) (args,out)) f Hspec).
           exact (Hwf g last' m' (eq_trans (eq_sym Hgd) HgetS'g) k Hk).
    - unfold wf_qc_state in *.
      intros g last' m' HgetS'g k Hk.
      cbn [fst snd] in HgetS'g.
      destruct (eqb g f) eqn:Hgf.
      + pose proof (@eqb_spec symbol Eqb_symbol Eqb_symbol_ok g f) as Hspec.
        rewrite Hgf in Hspec. subst g.
        assert (Hgps := @map.get_put_same symbol _ (symbol_map _) (symbol_map_ok _)
                          S f (idx_zero, map.singleton idx_zero (args, out))).
        assert (Heq := eq_trans (eq_sym Hgps) HgetS'g).
        injection Heq; intros Hm' Hlast'; subst last' m'.
        unfold map.singleton in Hk.
        destruct (eqb k idx_zero) eqn:Hk0.
        ++ pose proof (@eqb_spec idx Eqb_idx Eqb_idx_ok k idx_zero) as Hkspec.
           rewrite Hk0 in Hkspec. subst k. apply Hlts.
        ++ pose proof (@eqb_spec idx Eqb_idx Eqb_idx_ok k idx_zero) as Hkspec.
           rewrite Hk0 in Hkspec.
           assert (Hkd := @map.get_put_diff idx (list nat * nat) (idx_map _) (idx_map_ok _)
                            map.empty k (args,out) idx_zero Hkspec).
           assert (Hempty := @map.get_empty idx (list nat * nat) (idx_map _) (idx_map_ok _) k).
           exact (False_ind _ (Hk (eq_trans Hkd Hempty))).
      + pose proof (@eqb_spec symbol Eqb_symbol Eqb_symbol_ok g f) as Hspec.
        rewrite Hgf in Hspec.
        assert (Hgd := @map.get_put_diff symbol _ (symbol_map _) (symbol_map_ok _)
                         S g (idx_zero, map.singleton idx_zero (args,out)) f Hspec).
        exact (Hwf g last' m' (eq_trans (eq_sym Hgd) HgetS'g) k Hk).
  Qed.

  Lemma hash_clause_mono (Hlti : Asymmetric lt) :
    forall (a : Defs.atom nat symbol) (S : St), wf_qc_state S ->
    forall g j v, qc_entry S g j v -> qc_entry (snd (hash_clause idx idx_succ idx_zero symbol symbol_map idx_map a S)) g j v.
  Proof.
    intros [f args out] S Hwf g j v (last & m & HgetSg & HgetMj).
    unfold qc_entry.
    change St with (symbol_map (idx * idx_map (list nat * nat))) in *.
    unfold hash_clause. cbn [fst snd].
    destruct (map.get S f) as [ [last' m'] | ] eqn:HgetSf.
    - destruct (map_inverse_get m' (args, out)) as [r|] eqn:Hinv.
      + cbn [fst snd].
        exists last, m. split; [ exact HgetSg | exact HgetMj ].
      + cbn [fst snd].
        destruct (eqb g f) eqn:Hgf.
        ++ pose proof (@eqb_spec symbol Eqb_symbol Eqb_symbol_ok g f) as Hspec.
           rewrite Hgf in Hspec. subst g.
           assert (Hmm : last = last' /\ m = m').
           { rewrite HgetSf in HgetSg. injection HgetSg; intros; subst; auto. }
           destruct Hmm as [Hlast Hmeq]; subst m' last'.
           assert (Hlt_j : lt j (idx_succ last)) by
             (apply (Hwf f last m HgetSf j); intro H; rewrite H in HgetMj; discriminate HgetMj).
           assert (Hj_neq : j <> idx_succ last).
           { intro Heq; subst j. exact (Hlti _ _ Hlt_j Hlt_j). }
           assert (Hgps := @map.get_put_same symbol _ (symbol_map _) (symbol_map_ok _)
                             S f (idx_succ last, map.put m (idx_succ last) (args, out))).
           assert (Hkd := @map.get_put_diff idx (list nat * nat) (idx_map _) (idx_map_ok _)
                            m j (args,out) (idx_succ last) Hj_neq).
           exists (idx_succ last), (map.put m (idx_succ last) (args, out)). split.
           +++ exact Hgps.
           +++ exact (eq_trans Hkd HgetMj).
        ++ pose proof (@eqb_spec symbol Eqb_symbol Eqb_symbol_ok g f) as Hspec.
           rewrite Hgf in Hspec.
           assert (Hgd := @map.get_put_diff symbol _ (symbol_map _) (symbol_map_ok _)
                            S g (idx_succ last', map.put m' (idx_succ last') (args,out)) f Hspec).
           exists last, m. split.
           +++ exact (eq_trans Hgd HgetSg).
           +++ exact HgetMj.
    - cbn [fst snd].
      destruct (eqb g f) eqn:Hgf.
      + pose proof (@eqb_spec symbol Eqb_symbol Eqb_symbol_ok g f) as Hspec.
        rewrite Hgf in Hspec. subst g.
        rewrite HgetSf in HgetSg. discriminate HgetSg.
      + pose proof (@eqb_spec symbol Eqb_symbol Eqb_symbol_ok g f) as Hspec.
        rewrite Hgf in Hspec.
        assert (Hgd := @map.get_put_diff symbol _ (symbol_map _) (symbol_map_ok _)
                         S g (idx_zero, map.singleton idx_zero (args,out)) f Hspec).
        exists last, m. split.
        ++ exact (eq_trans Hgd HgetSg).
        ++ exact HgetMj.
  Qed.

  Lemma list_Mmap_qc_preserves {A B} (step : A -> state St B)
    (Hwf_step : forall a S, wf_qc_state S -> wf_qc_state (snd (step a S)))
    (Hmono_step : forall a S, wf_qc_state S -> forall g j v, qc_entry S g j v -> qc_entry (snd (step a S)) g j v) :
    forall (xs : list A) (S : St), wf_qc_state S ->
      wf_qc_state (snd (list_Mmap step xs S))
      /\ (forall g j v, qc_entry S g j v -> qc_entry (snd (list_Mmap step xs S)) g j v).
  Proof.
    induction xs as [|x xs' IH]; intros S Hs.
    - cbn [list_Mmap Mbind Mret StateMonad.state_monad fst snd].
      split; [ exact Hs | intros g j v H; exact H ].
    - cbn [list_Mmap Mbind Mret StateMonad.state_monad].
      destruct (step x S) as [y S1] eqn:Hstep.
      destruct (list_Mmap step xs' S1) as [ys S2] eqn:Hrec.
      cbn [fst snd].
      assert (HS1 : snd (step x S) = S1) by (rewrite Hstep; reflexivity).
      assert (HS2 : snd (list_Mmap step xs' S1) = S2) by (rewrite Hrec; reflexivity).
      rewrite <- HS1 in *.
      specialize (IH (snd (step x S)) (Hwf_step x S Hs)).
      rewrite HS2 in IH.
      rewrite <- HS2 in IH.
      split.
      + rewrite <- HS2. exact (proj1 IH).
      + intros g j v Hentry.
        rewrite <- HS2. apply (proj2 IH).
        apply (Hmono_step x S Hs g j v Hentry).
  Qed.

  Lemma compile_query_clause_preserves_wf (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt) :
    forall (qvs : list idx) (a : Defs.atom idx symbol) (S : St),
      wf_qc_state S ->
      wf_qc_state (snd (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs a S)).
  Proof.
    intros qvs [f args out] S Hs.
    unfold compile_query_clause.
    cbn [Mbind Mret StateMonad.state_monad].
    set (cc := {| atom_fn := f;
                  atom_args := map (named_list_lookup 0
                     (combine (sort_by_position_in idx Eqb_idx (out :: args) qvs)
                        (seq 0 (length (sort_by_position_in idx Eqb_idx (out :: args) qvs))))) args;
                  atom_ret := named_list_lookup 0
                     (combine (sort_by_position_in idx Eqb_idx (out :: args) qvs)
                        (seq 0 (length (sort_by_position_in idx Eqb_idx (out :: args) qvs)))) out |}).
    destruct (hash_clause idx idx_succ idx_zero symbol symbol_map idx_map cc S) as [i S'] eqn:Hhc.
    cbn [fst snd].
    assert (HS' : S' = snd (hash_clause idx idx_succ idx_zero symbol symbol_map idx_map cc S)).
    { rewrite Hhc. reflexivity. }
    rewrite HS'.
    apply (hash_clause_preserves_wf Hlts Hltt cc S Hs).
  Qed.

  Lemma compile_query_clause_mono (Hlti : Asymmetric lt) :
    forall (qvs : list idx) (a : Defs.atom idx symbol) (S : St),
      wf_qc_state S ->
      forall g j v, qc_entry S g j v ->
      qc_entry (snd (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs a S)) g j v.
  Proof.
    intros qvs [f args out] S Hs g j v Hentry.
    unfold compile_query_clause.
    cbn [Mbind Mret StateMonad.state_monad].
    set (cc := {| atom_fn := f;
                  atom_args := map (named_list_lookup 0
                     (combine (sort_by_position_in idx Eqb_idx (out :: args) qvs)
                        (seq 0 (length (sort_by_position_in idx Eqb_idx (out :: args) qvs))))) args;
                  atom_ret := named_list_lookup 0
                     (combine (sort_by_position_in idx Eqb_idx (out :: args) qvs)
                        (seq 0 (length (sort_by_position_in idx Eqb_idx (out :: args) qvs)))) out |}).
    destruct (hash_clause idx idx_succ idx_zero symbol symbol_map idx_map cc S) as [i S'] eqn:Hhc.
    cbn [fst snd].
    assert (HS' : S' = snd (hash_clause idx idx_succ idx_zero symbol symbol_map idx_map cc S)).
    { rewrite Hhc. reflexivity. }
    rewrite HS'.
    apply (hash_clause_mono Hlti cc S Hs g j v Hentry).
  Qed.

  Lemma compile_rule_preserves_wf
    (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt) (Hlti : Asymmetric lt) :
    forall rf (r : sequent) (S : St),
      wf_qc_state S ->
      wf_qc_state (snd (compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf r S)).
  Proof.
    intros rf r S Hs.
    unfold compile_rule.
    destruct (optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie r rf)
      as [ [assumptions conclusion_atoms] conclusion_eqs ].
    cbn [Mbind Mret StateMonad.state_monad fst snd].
    set (qvs := dedup eqb (flat_map (atom_fvs idx symbol) assumptions)).
    destruct (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs)
                assumptions S) as [qcls_ptrs S1] eqn:Hlm.
    cbn [fst snd].
    assert (HS1 : S1 = snd (list_Mmap
                     (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs)
                     assumptions S)) by (rewrite Hlm; reflexivity).
    destruct qcls_ptrs; cbn [fst snd]; rewrite HS1;
    exact (proj1 (list_Mmap_qc_preserves
      (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs)
      (compile_query_clause_preserves_wf Hlts Hltt qvs)
      (compile_query_clause_mono Hlti qvs)
      assumptions S Hs)).
  Qed.

  Lemma compile_rule_mono
    (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt) (Hlti : Asymmetric lt) :
    forall rf (r : sequent) (S : St),
      wf_qc_state S ->
      forall g j v, qc_entry S g j v ->
      qc_entry (snd (compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf r S)) g j v.
  Proof.
    intros rf r S Hs g j v Hentry.
    unfold compile_rule.
    destruct (optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie r rf)
      as [ [assumptions conclusion_atoms] conclusion_eqs ].
    cbn [Mbind Mret StateMonad.state_monad fst snd].
    set (qvs := dedup eqb (flat_map (atom_fvs idx symbol) assumptions)).
    destruct (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs)
                assumptions S) as [qcls_ptrs S1] eqn:Hlm.
    cbn [fst snd].
    assert (HS1 : S1 = snd (list_Mmap
                     (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs)
                     assumptions S)) by (rewrite Hlm; reflexivity).
    destruct qcls_ptrs; cbn [fst snd]; rewrite HS1;
    exact (proj2 (list_Mmap_qc_preserves
      (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs)
      (compile_query_clause_preserves_wf Hlts Hltt qvs)
      (compile_query_clause_mono Hlti qvs)
      assumptions S Hs) g j v Hentry).
  Qed.

  (* Combined result for the outer list_Mmap (compile_rule rf) rules loop *)
  Lemma build_rule_set_state_wf
    (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt) (Hlti : Asymmetric lt) :
    forall rf (rules : list sequent),
      wf_qc_state (snd (list_Mmap (compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf) rules map.empty)).
  Proof.
    intros rf rules.
    apply (proj1 (list_Mmap_qc_preserves
      (compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf)
      (compile_rule_preserves_wf Hlts Hltt Hlti rf)
      (compile_rule_mono Hlts Hltt Hlti rf)
      rules map.empty wf_qc_state_empty)).
  Qed.

  Lemma build_rule_set_state_mono
    (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt) (Hlti : Asymmetric lt) :
    forall rf (rules : list sequent),
      forall g j v, qc_entry map.empty g j v ->
      qc_entry (snd (list_Mmap (compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf) rules map.empty)) g j v.
  Proof.
    intros rf rules g j v Hentry.
    apply (proj2 (list_Mmap_qc_preserves
      (compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf)
      (compile_rule_preserves_wf Hlts Hltt Hlti rf)
      (compile_rule_mono Hlts Hltt Hlti rf)
      rules map.empty wf_qc_state_empty) g j v Hentry).
  Qed.

  (* ============================================================== *)
  (* E1: optimize_sequent fields parametric in rf                    *)
  (* ============================================================== *)

  Lemma optimize_sequent_fields_at : forall (r : sequent) (rf : nat),
    let '(assumptions, catoms, ceqs) :=
      QueryOpt.optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie r rf in
    (QueryOpt.optimize_sequent idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie r rf).(Semantics.seq_assumptions)
      = map (@atom_clause idx symbol) assumptions
    /\ (QueryOpt.optimize_sequent idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie r rf).(Semantics.seq_conclusions)
      = map (uncurry (@eq_clause idx symbol)) ceqs ++ map (@atom_clause idx symbol) catoms.
  Proof.
    intros r rf.
    unfold QueryOpt.optimize_sequent', QueryOpt.optimize_sequent, QueryOpt.sequent'_of_states, QueryOpt.sequent_of_states_seq.
    cbn. split; reflexivity.
  Qed.

  (* ============================================================== *)
  (* E2: compile_query_clause list round-trip                        *)
  (* ============================================================== *)

  Lemma list_Mmap_cqc_reconstruct
    (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
    (symbol_map_plus_ok : @map_plus_ok _ _ symbol_map_plus) :
    forall (qvs : list idx) (NDqvs : NoDup qvs)
           (assumptions : list (Defs.atom idx symbol))
           (Hsub : forall a, In a assumptions ->
                   forall x, In x (Defs.atom_ret a :: Defs.atom_args a) -> In x qvs)
           (S0 : St) (Hwf0 : wf_qc_state S0)
           (Qfin : St)
           (Hmono : forall g j v,
              qc_entry (snd (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) assumptions S0)) g j v
              -> qc_entry Qfin g j v),
      map (fun ptr => let '(Build_erule_query_ptr _ _ f n cv_list) := ptr in
             let '(cargs,cv) := match map.get (map_map snd Qfin) f with
               | Some q_f => match map.get q_f n with Some c => c | None => ([],0) end
               | None => ([],0) end in
             Build_atom f (map (fun k => nth k cv_list idx_zero) cargs) (nth cv cv_list idx_zero))
          (fst (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) assumptions S0))
        = assumptions.
  Proof.
    intros qvs NDqvs assumptions.
    induction assumptions as [|a rest IH].
    - intros. cbn [list_Mmap Mbind Mret StateMonad.state_monad fst map]. reflexivity.
    - intros Hsub S0 Hwf0 Qfin Hmono.
      cbn [list_Mmap Mbind Mret StateMonad.state_monad].
      destruct (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs a S0) as [ptr S1] eqn:Hcqc.
      destruct (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) rest S1) as [ptrs S2] eqn:Hrec.
      cbn [fst map].
      assert (HS1_snd : S1 = snd (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs a S0)) by (rewrite Hcqc; reflexivity).
      assert (Hwf_S1 : wf_qc_state S1) by (rewrite HS1_snd; apply (compile_query_clause_preserves_wf Hlts Hltt qvs a S0 Hwf0)).
      assert (Hmono' : forall g0 j0 v0,
          qc_entry (snd (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) rest S1)) g0 j0 v0
          -> qc_entry Qfin g0 j0 v0).
      { intros g0 j0 v0 Hentry.
        apply Hmono.
        cbn [list_Mmap Mbind Mret StateMonad.state_monad].
        rewrite Hcqc; cbn [fst snd]. rewrite Hrec; cbn [fst snd].
        rewrite Hrec in Hentry; cbn [snd] in Hentry. exact Hentry. }
      assert (Htail : map (fun ptr => let '(Build_erule_query_ptr _ _ f n cv_list) := ptr in
             let '(cargs,cv) := match map.get (map_map snd Qfin) f with
               | Some q_f => match map.get q_f n with Some c => c | None => ([],0) end
               | None => ([],0) end in
             Build_atom f (map (fun k => nth k cv_list idx_zero) cargs) (nth cv cv_list idx_zero)) ptrs = rest).
      { pose proof (IH (fun a' Hin' => Hsub a' (or_intror Hin')) S1 Hwf_S1 Qfin Hmono') as IHapp.
        rewrite Hrec in IHapp; cbn [fst] in IHapp. exact IHapp. }
      destruct a as [f args out].
      unfold compile_query_clause in Hcqc.
      cbn [Mbind Mret StateMonad.state_monad] in Hcqc.
      set (clause_vars := sort_by_position_in idx Eqb_idx (out :: args) qvs) in *.
      set (sub := combine clause_vars (seq 0 (length clause_vars))) in *.
      set (cc := {| atom_fn := f;
                    atom_args := map (named_list_lookup 0 sub) args;
                    atom_ret := named_list_lookup 0 sub out |}) in *.
      destruct (hash_clause idx idx_succ idx_zero symbol symbol_map idx_map cc S0) as [i S1'] eqn:Hhc.
      cbn [Mret StateMonad.state_monad] in Hcqc.
      assert (Hptr_eq : ptr = {| query_ptr_symbol := f; query_ptr_ptr := i; query_ptr_args := clause_vars |}).
      { injection Hcqc; intros _ Hp. exact (eq_sym Hp). }
      assert (HS1'_eq : S1' = S1).
      { injection Hcqc; intros HS _. exact HS. }
      cbn. rewrite Hptr_eq. cbn.
      pose proof (hash_clause_sets cc S0) as Hsets.
      cbn [Defs.atom_fn Defs.atom_args Defs.atom_ret] in Hsets.
      assert (HS1'snd : S1' = snd (hash_clause idx idx_succ idx_zero symbol symbol_map idx_map cc S0)) by (rewrite Hhc; reflexivity).
      assert (Hi_eq : i = fst (hash_clause idx idx_succ idx_zero symbol symbol_map idx_map cc S0)) by (rewrite Hhc; reflexivity).
      rewrite <- HS1'snd, <- Hi_eq in Hsets.
      rewrite HS1'_eq in Hsets.
      assert (Hwf_S1' : wf_qc_state S1').
      { rewrite HS1'snd. apply (hash_clause_preserves_wf Hlts Hltt cc S0 Hwf0). }
      pose proof (proj2 (list_Mmap_qc_preserves
        (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs)
        (compile_query_clause_preserves_wf Hlts Hltt qvs)
        (compile_query_clause_mono Hlti qvs)
        rest S1 Hwf_S1) f i _ Hsets) as Hentry_S2.
      assert (HS2eq : S2 = snd (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) rest S1)) by (rewrite Hrec; reflexivity).
      pose proof (Hmono' f i _ Hentry_S2) as Hentry_Qfin.
      destruct Hentry_Qfin as (last & m & HgetQf & HgetMi).
      rewrite (@map_map_spec symbol symbol_map symbol_map_plus symbol_map_plus_ok (idx * idx_map (list nat * nat)) (idx_map (list nat * nat)) snd Qfin f).
      assert (Hom : option_map snd (map.get Qfin f) = Some m) by (rewrite HgetQf; reflexivity).
      cbn [option_map] in Hom.
      change (match option_map snd (map.get Qfin f) with Some q_f => match map.get q_f i with Some c => c | None => ([], 0) end | None => ([], 0) end) with (match option_map snd (map.get Qfin f) with Some q_f => match map.get q_f i with Some c => c | None => ([], 0) end | None => ([], 0) end).
      rewrite Hom. rewrite HgetMi. cbn [atom_args atom_ret].
      assert (Hargs : map (fun k => nth k clause_vars idx_zero) (atom_args cc) = args).
      { unfold clause_vars, sub. apply map_nth_named_list_lookup_combine_seq.
        { apply NoDup_filter. exact NDqvs. }
        { intros x Hx. apply filter_In. split.
          { apply (Hsub {| atom_fn := f; atom_args := args; atom_ret := out |}).
            { left. reflexivity. } { right. exact Hx. } }
          { apply Is_true_implies_eq_true.
            apply (proj2 (@inb_is_In idx Eqb_idx Eqb_idx_ok x (out :: args))).
            right. exact Hx. } } }
      assert (Hret : nth (atom_ret cc) clause_vars idx_zero = out).
      { unfold clause_vars, sub. apply nth_named_list_lookup_combine_seq.
        { apply NoDup_filter. exact NDqvs. }
        { apply filter_In. split.
          { apply (Hsub {| atom_fn := f; atom_args := args; atom_ret := out |}).
            { left. reflexivity. } { left. reflexivity. } }
          { apply Is_true_implies_eq_true.
            apply (proj2 (@inb_is_In idx Eqb_idx Eqb_idx_ok out (out :: args))).
            left. reflexivity. } } }
      rewrite Hargs. rewrite Hret.
      f_equal. exact Htail.
  Qed.

  (* ============================================================== *)
  (* E3: query_atoms of compiled rule = optimize_sequent' assumptions *)
  (* ============================================================== *)

  Lemma query_atoms_compile_rule_eq
    (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
    (symbol_map_plus_ok : @map_plus_ok _ _ symbol_map_plus) :
    forall (rf : nat) (rule : sequent) (st0 st1 : St) (er : erule idx symbol) (Qfin : St),
      wf_qc_state st0 ->
      compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf rule st0 = (inl er, st1) ->
      (forall g j v, qc_entry st1 g j v -> qc_entry Qfin g j v) ->
      Semantics.query_atoms idx idx_zero symbol symbol_map idx_map (map_map snd Qfin) er
        = (let '(assumptions,_,_) := QueryOpt.optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rule rf in assumptions).
  Proof.
    intros rf rule st0 st1 er Qfin Hwf0 Hc Hmono.
    unfold compile_rule in Hc.
    destruct (QueryOpt.optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rule rf)
      as [ [assumptions catoms] ceqs ] eqn:Hopt.
    set (qvs := dedup eqb (flat_map (atom_fvs idx symbol) assumptions)) in *.
    destruct (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) assumptions st0)
      as [qcls_ptrs st'] eqn:Hmap.
    cbn [Mbind StateMonad.state_monad] in Hc.
    rewrite Hmap in Hc.
    destruct qcls_ptrs as [| c cs].
    - cbn [Mret StateMonad.state_monad] in Hc. inversion Hc.
    - cbn [Mret StateMonad.state_monad] in Hc. inversion Hc.
      subst st1. subst er.
      cbn [Semantics.query_atoms query_clause_ptrs uncurry].
      unfold Semantics.query_atoms.
      cbn [query_clause_ptrs uncurry].
      change (map (fun '{| query_ptr_symbol := f; query_ptr_ptr := n; query_ptr_args := cv_list |} =>
               let '(cargs,cv) := match map.get (map_map snd Qfin) f with
                 | Some q_f => match map.get q_f n with Some c => c | None => ([],0) end
                 | None => ([],0) end in
               {| atom_fn := f; atom_args := map (fun k => nth k cv_list idx_zero) cargs; atom_ret := nth cv cv_list idx_zero |})
               (c :: cs))
        with (map (fun ptr => let '(Build_erule_query_ptr _ _ f n cv_list) := ptr in
               let '(cargs,cv) := match map.get (map_map snd Qfin) f with
                 | Some q_f => match map.get q_f n with Some c => c | None => ([],0) end
                 | None => ([],0) end in
               Build_atom f (map (fun k => nth k cv_list idx_zero) cargs) (nth cv cv_list idx_zero))
               (c :: cs)).
      assert (Hfst : fst (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) assumptions st0) = c :: cs).
      { rewrite Hmap. reflexivity. }
      rewrite <- Hfst.
      apply (list_Mmap_cqc_reconstruct Hlti Hlts Hltt symbol_map_plus_ok qvs).
      1: apply NoDup_dedup; exact (@eqb_boolspec idx Eqb_idx Eqb_idx_ok).
      1: { intros a Hina x Hx. unfold qvs.
           apply (proj1 (@dedup_preserves_In idx eqb (@eqb_boolspec idx Eqb_idx Eqb_idx_ok) (flat_map (atom_fvs idx symbol) assumptions) x)).
           apply (proj2 (in_flat_map (atom_fvs idx symbol) assumptions x)).
           exact (ex_intro _ a (conj Hina Hx)). }
      1: exact Hwf0.
      1: { intros g j v Hentry.
           apply Hmono.
           assert (Hsnd : snd (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) assumptions st0) = st').
           { rewrite Hmap. reflexivity. }
           rewrite Hsnd in Hentry. exact Hentry. }
  Qed.

  (* ============================================================== *)
  (* E4: forall_vars of optimize_sequent ↔ dedup atom_fvs of assums *)
  (* ============================================================== *)

  Lemma forall_vars_optimize_sequent_eq_qvs :
    forall (rf : nat) (rule : sequent),
      let assumptions := (let '(a,_,_) := QueryOpt.optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rule rf in a) in
      forall y, In y (Semantics.forall_vars (QueryOpt.optimize_sequent idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rule rf))
            <-> In y (dedup (eqb (A:=idx)) (flat_map (QueryOpt.atom_fvs idx symbol) assumptions)).
  Proof.
    intros rf rule y.
    unfold Semantics.forall_vars.
    pose proof (optimize_sequent_fields_at rule rf) as Hfields.
    destruct (QueryOpt.optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rule rf)
      as [ [assumptions catoms] ceqs ] eqn:Hopt.
    destruct Hfields as [Hassm _].
    rewrite Hassm.
    assert (Heq : flat_map (Semantics.clause_vars idx symbol) (map (@atom_clause idx symbol) assumptions) = flat_map (QueryOpt.atom_fvs idx symbol) assumptions).
    { rewrite flat_map_concat_map. rewrite List.map_map.
      rewrite <- flat_map_concat_map. apply flat_map_ext.
      intros a. destruct a. reflexivity. }
    intros y0. rewrite Heq.
    split.
    - apply (proj1 (@dedup_preserves_In idx eqb (@eqb_boolspec idx Eqb_idx Eqb_idx_ok) _ y0)).
    - apply (proj2 (@dedup_preserves_In idx eqb (@eqb_boolspec idx Eqb_idx Eqb_idx_ok) _ y0)).
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

  Lemma split_sum_list_in_snd :
    forall (A B : Type) (l : list (A + B)) (b : B),
      In b (snd (split_sum_list l)) <-> In (inr b) l.
  Proof.
    intros A B l b.
    induction l as [|h t IH].
    - cbn. tauto.
    - cbn [split_sum_list List.fold_right].
      destruct h as [a' | b'].
      + cbn [snd In].
        rewrite IH.
        split.
        * intros Hin. right. exact Hin.
        * intros [Heq | Hin].
          -- discriminate Heq.
          -- exact Hin.
      + cbn [snd In].
        rewrite IH.
        split.
        * intros [Heq | Hin].
          -- left. congruence.
          -- right. exact Hin.
        * intros [Heq | Hin].
          -- left. injection Heq. auto.
          -- right. exact Hin.
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

  Lemma list_Mmap_state_length :
    forall (Xt St0 Yt : Type) (f : Xt -> state St0 Yt) (xs : list Xt) (s0 : St0),
      List.length (fst (list_Mmap f xs s0)) = List.length xs.
  Proof.
    intros Xt St0 Yt f xs.
    induction xs as [|x xs IH]; intros s0.
    - cbn. reflexivity.
    - cbn [list_Mmap Mbind Mret StateMonad.state_monad].
      destruct (f x s0) as [y0 s'] eqn:Hf.
      destruct (list_Mmap f xs s') as [ys s''] eqn:Hrec.
      cbn [fst List.length].
      f_equal.
      specialize (IH s').
      rewrite Hrec in IH. cbn [fst] in IH.
      exact IH.
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

  Lemma in_compiled_const_rules_build_rule_set :
    forall (rf : nat) (rules : list sequent)
           (cr : const_rule idx symbol),
      In cr (compiled_const_rules idx symbol symbol_map idx_map
               (build_rule_set idx_succ idx_zero rf rules)) ->
      exists rule st0 st1,
        In rule rules /\
        compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf rule st0 = (inr cr, st1).
  Proof.
    intros rf rules cr Hin.
    unfold build_rule_set in Hin.
    destruct (list_Mmap (compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf) rules map.empty)
      as [crs cp] eqn:Hlm.
    destruct (split_sum_list crs) as [erules consts] eqn:Hssl.
    cbn [compiled_const_rules] in Hin.
    assert (Hconsts : consts = snd (split_sum_list crs)).
    { rewrite Hssl. reflexivity. }
    rewrite Hconsts in Hin.
    apply split_sum_list_in_snd in Hin.
    assert (Hcrs : crs = fst (list_Mmap (compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf) rules map.empty)).
    { rewrite Hlm. reflexivity. }
    rewrite Hcrs in Hin.
    apply list_Mmap_state_in in Hin.
    destruct Hin as (rule & s & s' & Hrule_in & Hcompile).
    exists rule, s, s'.
    exact (conj Hrule_in Hcompile).
  Qed.

  (* ============================================================== *)
  (* M1: list_Mmap_state_in_mono                                     *)
  (* Generic suffix-monotonicity for list_Mmap                       *)
  (* ============================================================== *)

  Lemma list_Mmap_state_in_mono
    {Y : Type}
    (step : sequent -> state St Y)
    (Hwf : forall a (S : St), wf_qc_state S -> wf_qc_state (snd (step a S)))
    (Hmono : forall a (S : St), wf_qc_state S -> forall g j v, qc_entry S g j v -> qc_entry (snd (step a S)) g j v) :
    forall (xs : list sequent) (s0 : St) (y : Y),
      wf_qc_state s0 ->
      In y (fst (list_Mmap step xs s0)) ->
      exists x s s', In x xs /\ step x s = (y, s') /\ wf_qc_state s /\
        (forall g j v, qc_entry s' g j v ->
           qc_entry (snd (list_Mmap step xs s0)) g j v).
  Proof.
    induction xs as [|x xs' IH]; intros s0 y Hwf0 Hin.
    - cbn [list_Mmap Mbind Mret StateMonad.state_monad fst] in Hin. destruct Hin.
    - cbn [list_Mmap Mbind Mret StateMonad.state_monad] in Hin.
      destruct (step x s0) as [y0 s1] eqn:Hstep.
      destruct (list_Mmap step xs' s1) as [ys s2] eqn:Hrec.
      cbn [fst] in Hin.
      cbn [In] in Hin.
      assert (Hs1wf : wf_qc_state s1).
      { assert (Heqs1 : s1 = snd (step x s0)) by (rewrite Hstep; reflexivity).
        rewrite Heqs1. exact (Hwf x s0 Hwf0). }
      assert (Hs2 : s2 = snd (list_Mmap step xs' s1)).
      { rewrite Hrec. reflexivity. }
      assert (Hsnd_total : snd (list_Mmap step (x :: xs') s0) = s2).
      { cbn [list_Mmap Mbind Mret StateMonad.state_monad snd].
        rewrite Hstep. rewrite Hrec. reflexivity. }
      destruct Hin as [Heq | Hin].
      + (* head case: y = y0 *)
        subst y0.
        exists x, s0, s1.
        split. { left. reflexivity. }
        split. { exact Hstep. }
        split. { exact Hwf0. }
        intros g j v Hentry.
        rewrite Hsnd_total. rewrite Hs2.
        exact (proj2 (list_Mmap_qc_preserves step Hwf Hmono xs' s1 Hs1wf) g j v Hentry).
      + (* tail case: y in ys *)
        assert (Hin' : In y (fst (list_Mmap step xs' s1))).
        { rewrite Hrec. cbn [fst]. exact Hin. }
        specialize (IH s1 y Hs1wf Hin') as (x' & s & s' & Hxin & Hstep' & Hwfs & Hmono').
        exists x', s, s'.
        split. { right. exact Hxin. }
        split. { exact Hstep'. }
        split. { exact Hwfs. }
        intros g j v Hentry.
        rewrite Hsnd_total. rewrite Hs2.
        exact (Hmono' g j v Hentry).
  Qed.

  (* ============================================================== *)
  (* M2: in_compiled_rules_build_rule_set_mono                       *)
  (* Strengthened version tracking suffix-monotonicity to global St  *)
  (* ============================================================== *)

  Lemma in_compiled_rules_build_rule_set_mono
    (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt) :
    forall (rf : nat) (rules : list sequent) (er : erule idx symbol),
      In er (compiled_rules idx symbol symbol_map idx_map
               (build_rule_set idx_succ idx_zero rf rules)) ->
      exists rule st0 st1,
        In rule rules /\
        compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf rule st0 = (inl er, st1) /\
        wf_qc_state st0 /\
        (forall g j v, qc_entry st1 g j v ->
           qc_entry (snd (list_Mmap (compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf) rules map.empty)) g j v).
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
    pose proof (list_Mmap_state_in_mono
      (compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf)
      (fun a S HS => compile_rule_preserves_wf Hlts Hltt Hlti rf a S HS)
      (fun a S HS g j v Hentry => compile_rule_mono Hlts Hltt Hlti rf a S HS g j v Hentry)
      rules map.empty (inl er) wf_qc_state_empty Hin)
      as (rule & st0 & st1 & Hrule_in & Hcompile & Hwf0 & Hmono_fin).
    exists rule, st0, st1.
    split. { exact Hrule_in. }
    split. { exact Hcompile. }
    split. { exact Hwf0. }
    intros g j v Hentry.
    rewrite <- Hlm.
    exact (Hmono_fin g j v Hentry).
  Qed.

  (* ============================================================== *)
  (* M3: query_atoms_build_rule_set_eq                               *)
  (* Build_rule_set-level assumption alignment                        *)
  (* ============================================================== *)

  Lemma query_atoms_build_rule_set_eq
    (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
    (symbol_map_plus_ok : @map_plus_ok _ _ symbol_map_plus) :
    forall (rf : nat) (rules : list sequent) (er : erule idx symbol),
      In er (compiled_rules idx symbol symbol_map idx_map
               (build_rule_set idx_succ idx_zero rf rules)) ->
      exists rule, In rule rules /\
        Semantics.query_atoms idx idx_zero symbol symbol_map idx_map
          (query_clauses idx symbol symbol_map idx_map
             (build_rule_set idx_succ idx_zero rf rules)) er
        = (let '(a,_,_) := QueryOpt.optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rule rf in a).
  Proof.
    intros rf rules er Hin.
    pose proof (in_compiled_rules_build_rule_set_mono Hlti Hlts Hltt rf rules er Hin)
      as (rule & st0 & st1 & Hrule_in & Hcompile & Hwf0 & Hmono_fin).
    exists rule.
    split. { exact Hrule_in. }
    (* Establish that query_clauses (build_rule_set rf rules) = map_map snd Qfin *)
    destruct (list_Mmap (compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf) rules map.empty)
      as [crs cp] eqn:Hlm.
    assert (Hqc : query_clauses idx symbol symbol_map idx_map (build_rule_set idx_succ idx_zero rf rules) = map_map snd cp).
    { unfold build_rule_set.
      rewrite Hlm.
      destruct (split_sum_list crs) as [erules consts].
      cbn [query_clauses]. reflexivity. }
    assert (Hmono_fin' : forall g j v, qc_entry st1 g j v -> qc_entry cp g j v).
    { intros g j v Hentry. exact (Hmono_fin g j v Hentry). }
    rewrite Hqc.
    exact (query_atoms_compile_rule_eq Hlti Hlts Hltt symbol_map_plus_ok rf rule st0 st1 er cp Hwf0 Hcompile Hmono_fin').
  Qed.

  (* ============================================================== *)
  (* A1: compile_rule_inl_fields                                      *)
  (* er field identities from compile_rule = (inl er, st1)           *)
  (* ============================================================== *)

  Lemma compile_rule_inl_fields :
    forall rf r st0 er st1,
      compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf r st0 = (inl er, st1) ->
      let '(assumptions, catoms, ceqs) :=
        QueryOpt.optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie r rf in
      query_vars idx symbol er = dedup (eqb (A:=idx)) (flat_map (QueryOpt.atom_fvs idx symbol) assumptions)
      /\ write_clauses idx symbol er = catoms
      /\ write_unifications idx symbol er = ceqs.
  Proof.
    intros rf r st0 er st1 Hc.
    unfold compile_rule in Hc.
    destruct (QueryOpt.optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie r rf)
      as [ [assumptions catoms] ceqs ] eqn:Hopt.
    set (qvs := dedup (eqb (A:=idx)) (flat_map (atom_fvs idx symbol) assumptions)) in *.
    destruct (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) assumptions st0)
      as [qcls_ptrs st'] eqn:Hmap.
    cbn [Mbind StateMonad.state_monad] in Hc.
    rewrite Hmap in Hc.
    destruct qcls_ptrs as [| c cs].
    - cbn [Mret StateMonad.state_monad] in Hc. inversion Hc.
    - cbn [Mret StateMonad.state_monad] in Hc. inversion Hc; subst.
      cbn [query_vars write_clauses write_unifications].
      repeat split; reflexivity.
  Qed.

  Lemma compile_rule_inr_fields :
    forall rf r st0 cr st1,
      compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf r st0 = (inr cr, st1) ->
      let '(assumptions, catoms, ceqs) :=
        QueryOpt.optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie r rf in
      assumptions = []
      /\ const_clauses idx symbol cr = catoms
      /\ const_unifications idx symbol cr = ceqs
      /\ const_vars idx symbol cr =
           clauses_fvs idx Eqb_idx symbol
             (map (uncurry (@eq_clause idx symbol)) ceqs ++ map (@atom_clause idx symbol) catoms)
             (dedup (eqb (A:=idx)) (flat_map (QueryOpt.atom_fvs idx symbol) assumptions)).
  Proof.
    intros rf r st0 cr st1 Hc.
    unfold compile_rule in Hc.
    destruct (QueryOpt.optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie r rf)
      as [ [assumptions catoms] ceqs ] eqn:Hopt.
    set (qvs := dedup (eqb (A:=idx)) (flat_map (atom_fvs idx symbol) assumptions)) in *.
    destruct (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) assumptions st0)
      as [qcls_ptrs st'] eqn:Hmap.
    cbn [Mbind StateMonad.state_monad] in Hc.
    rewrite Hmap in Hc.
    destruct qcls_ptrs as [| c cs].
    - cbn [Mret StateMonad.state_monad] in Hc. inversion Hc; subst.
      cbn [const_vars const_clauses const_unifications].
      assert (Hassm : assumptions = []).
      { pose proof (list_Mmap_state_length _ _ _
          (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs)
          assumptions st0) as Hlen.
        rewrite Hmap in Hlen. cbn [fst List.length] in Hlen.
        destruct assumptions as [|a0 ass]; [reflexivity | cbn in Hlen; discriminate]. }
      repeat split. exact Hassm.
    - cbn [Mret StateMonad.state_monad] in Hc. discriminate Hc.
  Qed.

  (* ============================================================== *)
  (* A2: compiled_rules_erule_sound                                   *)
  (* erule_sound for every compiled rule of a build_rule_set          *)
  (* ============================================================== *)

  Lemma compiled_rules_erule_sound
    (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
    (symbol_map_plus_ok : @map_plus_ok _ _ symbol_map_plus) :
    forall (m : model symbol) (Hm : model_ok symbol m)
           (rf : nat) (rules : list sequent) (er : erule idx symbol),
      (forall rule, In rule rules ->
         model_satisfies_rule m
           (QueryOpt.optimize_sequent idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rule rf)) ->
      In er (compiled_rules idx symbol symbol_map idx_map
               (build_rule_set idx_succ idx_zero rf rules)) ->
      Semantics.erule_sound idx idx_zero symbol symbol_map idx_map m
        (query_clauses idx symbol symbol_map idx_map
           (build_rule_set idx_succ idx_zero rf rules)) er.
  Proof.
    intros m Hm rf rules er Hmsr_all Hin.
    destruct (in_compiled_rules_build_rule_set_mono Hlti Hlts Hltt rf rules er Hin)
      as (rule & st0 & st1 & Hin_rule & Hcompile & Hwf0 & Hmono_fin).
    (* Set Qfin and establish query_clauses alignment *)
    destruct (list_Mmap (compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf)
                rules map.empty) as [crs cp] eqn:Hlm.
    set (Qfin := cp).
    assert (Hqc : query_clauses idx symbol symbol_map idx_map (build_rule_set idx_succ idx_zero rf rules)
                  = map_map snd Qfin).
    { unfold build_rule_set. rewrite Hlm.
      destruct (split_sum_list crs) as [erules consts].
      cbn [query_clauses]. reflexivity. }
    rewrite Hqc.
    assert (Hmono_fin' : forall g j v, qc_entry st1 g j v -> qc_entry Qfin g j v).
    { intros g j v Hentry. exact (Hmono_fin g j v Hentry). }
    (* Get er field identities *)
    pose proof (compile_rule_inl_fields rf rule st0 er st1 Hcompile) as Hfields.
    destruct (QueryOpt.optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rule rf)
      as [ [assumptions catoms] ceqs ] eqn:Hopt.
    destruct Hfields as (Hqv & Hwc & Hwu).
    (* Set sopt := optimize_sequent rule rf *)
    set (sopt := QueryOpt.optimize_sequent idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rule rf).
    (* Align assumptions *)
    pose proof (query_atoms_compile_rule_eq Hlti Hlts Hltt symbol_map_plus_ok rf rule st0 st1 er Qfin Hwf0 Hcompile Hmono_fin')
      as Hqa.
    rewrite Hopt in Hqa.
    pose proof (optimize_sequent_fields_at rule rf) as Hfields2.
    rewrite Hopt in Hfields2.
    destruct Hfields2 as (Hassm & Hconc).
    assert (Halign_assum :
      map (@atom_clause idx symbol)
          (Semantics.query_atoms idx idx_zero symbol symbol_map idx_map (map_map snd Qfin) er)
        = sopt.(Semantics.seq_assumptions)).
    { rewrite Hqa. unfold sopt. exact (eq_sym Hassm). }
    (* Align conclusions *)
    assert (Halign_concl :
      sopt.(Semantics.seq_conclusions) =
        map (uncurry (@eq_clause idx symbol)) (write_unifications idx symbol er)
        ++ map (@atom_clause idx symbol) (write_clauses idx symbol er)).
    { unfold sopt. rewrite Hconc. rewrite Hwu. rewrite Hwc. reflexivity. }
    (* Variable alignment *)
    assert (Hvars_eq : forall x, In x (Semantics.forall_vars sopt) <-> In x (query_vars idx symbol er)).
    { intros x.
      pose proof (forall_vars_optimize_sequent_eq_qvs rf rule) as Hvfvs.
      rewrite Hopt in Hvfvs.
      specialize (Hvfvs x).
      rewrite Hqv.
      exact Hvfvs. }
    (* Apply keystone *)
    exact (compile_rule_inl_erule_sound rf rule st0 er st1 m Hm (map_map snd Qfin) sopt
             Hcompile Halign_assum Halign_concl Hvars_eq (Hmsr_all rule Hin_rule)).
  Qed.

  (* ============================================================== *)
  (* A3: compile_rule_inr_const_sound                                 *)
  (* const_rule_sound for every compiled const-rule of build_rule_set *)
  (* ============================================================== *)

  Lemma compile_rule_inr_const_sound :
    forall (m : model symbol) (Hm : Semantics.model_ok symbol m)
           (rf : nat) (rules : list sequent) (cr : const_rule idx symbol),
      (forall rule, In rule rules ->
         model_satisfies_rule m
           (QueryOpt.optimize_sequent idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rule rf)) ->
      In cr (compiled_const_rules idx symbol symbol_map idx_map
               (build_rule_set idx_succ idx_zero rf rules)) ->
      exists a_src, const_rule_sound (m := m) a_src cr.
  Proof.
    intros m Hm rf rules cr Hmsr_all Hin.
    destruct (in_compiled_const_rules_build_rule_set rf rules cr Hin)
      as (rule & st0 & st1 & Hin_rule & Hcompile).
    specialize (Hmsr_all rule Hin_rule).
    set (sopt := QueryOpt.optimize_sequent idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rule rf) in *.
    pose proof (compile_rule_inr_fields rf rule st0 cr st1 Hcompile) as Hfields.
    pose proof (optimize_sequent_fields_at rule rf) as Hflds.
    destruct (QueryOpt.optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rule rf)
      as [ [assumptions catoms] ceqs ] eqn:Hopt.
    destruct Hfields as (Hassum_nil & Hcc & Hcu & Hcv).
    destruct Hflds as (Hsa & Hsc).
    subst assumptions.
    cbn [flat_map] in Hcv.
    (* concl *)
    set (concl := map (uncurry (@eq_clause idx symbol)) ceqs ++ map (@atom_clause idx symbol) catoms) in *.
    (* forall_vars sopt = [] *)
    assert (Hfv : Semantics.forall_vars sopt = []) by (unfold Semantics.forall_vars; unfold sopt; rewrite Hsa; reflexivity).
    (* Apply Hmsr at the empty assignment *)
    pose (ae := map.empty : idx_map (Semantics.domain symbol m)).
    specialize (Hmsr_all ae).
    assert (Hpre1 : forall x, In x (Semantics.forall_vars sopt) -> Sep.has_key x ae) by (rewrite Hfv; intros x []).
    assert (Hpre2 : forall x, Sep.has_key x ae -> In x (Semantics.forall_vars sopt)).
    { intros x Hk. unfold Sep.has_key, ae in Hk. rewrite map.get_empty in Hk.
      destruct Hk. }
    assert (Hpre3 : all (Semantics.clause_sound_for_model idx symbol idx_map m ae) sopt.(Semantics.seq_assumptions)).
    { unfold sopt. rewrite Hsa. cbn. exact I. }
    specialize (Hmsr_all Hpre1 Hpre2 Hpre3).
    destruct Hmsr_all as (a' & Hext & Hconcl_snd).
    unfold sopt in Hconcl_snd. rewrite Hsc in Hconcl_snd. fold concl in Hconcl_snd.
    pose proof Hconcl_snd as Hconcl_all.
    apply (all_app (Semantics.clause_sound_for_model idx symbol idx_map m a')) in Hconcl_snd.
    destruct Hconcl_snd as (Heq_snd & Hat_snd).
    exists a'.
    unfold const_rule_sound.
    (* conjunct 1 *)
    split.
    { rewrite Hcv. unfold QueryOpt.clauses_fvs. apply NoDup_filter. apply NoDup_dedup. }
    split.
    (* conjunct 2 *)
    { rewrite Hcv. intros x Hx.
      unfold QueryOpt.clauses_fvs in Hx. apply filter_In in Hx. destruct Hx as (Hx_dd & _).
      apply (proj2 (@dedup_preserves_In idx eqb (eqb_boolspec idx) _ x)) in Hx_dd.
      apply in_flat_map in Hx_dd. destruct Hx_dd as (c0 & Hc0_in & Hx_in).
      pose proof (in_all _ _ _ Hconcl_all Hc0_in) as Hc0_snd.
      exact (clause_sound_for_model_wf_var m Hm a' c0 x Hx_in Hc0_snd). }
    split.
    (* conjunct 3 *)
    { rewrite Hcc, Hcv. intros c Hc_in x Hx.
      unfold QueryOpt.clauses_fvs. apply filter_In. split.
      - apply (proj1 (@dedup_preserves_In idx eqb (eqb_boolspec idx) _ x)).
        apply in_flat_map. exists (@atom_clause idx symbol c). split.
        + apply in_app_iff. right. apply in_map_iff. exists c. split; [reflexivity | exact Hc_in].
        + cbn [Semantics.clause_vars]. exact Hx.
      - cbn. reflexivity. }
    split.
    (* conjunct 4 *)
    { rewrite Hcu, Hcv. intros [x y] Hxy. cbn [fst snd].
      split.
      - unfold QueryOpt.clauses_fvs. apply filter_In. split.
        + apply (proj1 (@dedup_preserves_In idx eqb (eqb_boolspec idx) _ x)).
          apply in_flat_map. exists (@eq_clause idx symbol x y). split.
          * apply in_app_iff. left. apply in_map_iff. exists (x, y). split; [reflexivity | exact Hxy].
          * cbn [Semantics.clause_vars]. left. reflexivity.
        + cbn. reflexivity.
      - unfold QueryOpt.clauses_fvs. apply filter_In. split.
        + apply (proj1 (@dedup_preserves_In idx eqb (eqb_boolspec idx) _ y)).
          apply in_flat_map. exists (@eq_clause idx symbol x y). split.
          * apply in_app_iff. left. apply in_map_iff. exists (x, y). split; [reflexivity | exact Hxy].
          * cbn [Semantics.clause_vars]. right. left. reflexivity.
        + cbn. reflexivity. }
    split.
    (* conjunct 5 *)
    { rewrite Hcc.
      clear - Hat_snd.
      induction catoms as [|c cs IH]; cbn in *; [exact I|].
      destruct Hat_snd as (Hc & Hcs).
      split; [exact Hc | exact (IH Hcs)]. }
    (* conjunct 6 *)
    { rewrite Hcu.
      clear - Heq_snd.
      induction ceqs as [|p ps IH]; cbn in *; [exact I|].
      destruct Heq_snd as (Hp & Hps).
      destruct p as [x y]. cbn in Hp |- *.
      split; [exact Hp | exact (IH Hps)]. }
  Qed.

  (* ============================================================== *)
  (* P0: named_list_lookup position bound                             *)
  (* ============================================================== *)

  Lemma P0_gen : forall (l : list idx) (base : nat) (x0 : idx),
      named_list_lookup 0 (combine l (seq base (length l))) x0 = 0 \/
      (base <= named_list_lookup 0 (combine l (seq base (length l))) x0 /\
       named_list_lookup 0 (combine l (seq base (length l))) x0 < base + length l).
  Proof.
    induction l as [|h t IH]; intros base x0.
    - cbn. left. reflexivity.
    - cbn [length seq combine named_list_lookup].
      destruct (eqb x0 h) eqn:Heq.
      + right. split; Lia.lia.
      + specialize (IH (S base) x0).
        destruct IH as [IH | (Hge & Hlt)].
        * left. exact IH.
        * right. split; Lia.lia.
  Qed.

  Lemma named_list_lookup_combine_seq_lt :
    forall (l : list idx) (x : idx), 0 < length l ->
      named_list_lookup 0 (combine l (seq 0 (length l))) x < length l.
  Proof.
    intros l x Hlen.
    pose proof (P0_gen l 0 x) as [H | (Hge & Hlt)].
    - rewrite H. exact Hlen.
    - Lia.lia.
  Qed.

  (* ============================================================== *)
  (* P1: per-ptr validity for list_Mmap compile_query_clause        *)
  (* ============================================================== *)

  Lemma list_Mmap_cqc_ptr_valid
    (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt) :
    forall (qvs : list idx) (NDqvs : NoDup qvs)
           (assumptions : list (Defs.atom idx symbol))
           (Hsub : forall a, In a assumptions -> forall x, In x (Defs.atom_ret a :: Defs.atom_args a) -> In x qvs)
           (S0 : St) (Hwf0 : wf_qc_state S0)
           (Qfin : St)
           (Hmono : forall g j v,
              qc_entry (snd (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) assumptions S0)) g j v -> qc_entry Qfin g j v),
      forall fsym nptr cvars,
        In (Build_erule_query_ptr idx symbol fsym nptr cvars)
           (fst (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) assumptions S0)) ->
        exists cargs cv,
          qc_entry Qfin fsym nptr (cargs, cv)
          /\ (exists Pf : idx -> bool, cvars = filter Pf qvs)
          /\ (forall t, In t cargs -> t < length cvars)
          /\ cv < length cvars.
  Proof.
    induction assumptions as [|a rest IH]; intros Hsub S0 Hwf0 Qfin Hmono fsym nptr cvars Hin.
    - cbn [list_Mmap Mbind Mret StateMonad.state_monad fst] in Hin. destruct Hin.
    - cbn [list_Mmap Mbind Mret StateMonad.state_monad] in Hin.
      destruct (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs a S0) as [ptr S1] eqn:Hcqc.
      destruct (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) rest S1) as [ptrs S2] eqn:Hrec.
      cbn [fst] in Hin.
      assert (Hmono' : forall g j v,
          qc_entry (snd (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) rest S1)) g j v ->
          qc_entry Qfin g j v).
      { intros g j v Hentry.
        apply Hmono.
        cbn [list_Mmap Mbind Mret StateMonad.state_monad].
        rewrite Hcqc; cbn [fst snd]. rewrite Hrec; cbn [snd].
        rewrite Hrec in Hentry; cbn [snd] in Hentry. exact Hentry. }
      assert (Hwf_S1_gen : wf_qc_state S1).
      { assert (HS1snd : S1 = snd (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs a S0)) by (rewrite Hcqc; reflexivity).
        rewrite HS1snd. apply (compile_query_clause_preserves_wf Hlts Hltt qvs a S0 Hwf0). }
      destruct Hin as [Heq | Hrest].
      + destruct a as [f args out].
        unfold compile_query_clause in Hcqc.
        cbn [Mbind Mret StateMonad.state_monad] in Hcqc.
        set (clause_vars := sort_by_position_in idx Eqb_idx (out :: args) qvs) in *.
        set (sub := combine clause_vars (seq 0 (length clause_vars))) in *.
        set (cc := {| atom_fn := f;
                      atom_args := map (named_list_lookup 0 sub) args;
                      atom_ret := named_list_lookup 0 sub out |}) in *.
        destruct (hash_clause idx idx_succ idx_zero symbol symbol_map idx_map cc S0) as [i S1'] eqn:Hhc.
        cbn [Mret StateMonad.state_monad] in Hcqc.
        injection Hcqc as HS1'S1 Hptr_eq.
        subst S1'.
        rewrite <- HS1'S1 in Heq.
        injection Heq as Hcv Hi Hf.
        subst fsym. subst nptr. subst cvars.
        assert (Hwf_S1 : wf_qc_state S1).
        { assert (HS1snd : S1 = snd (hash_clause idx idx_succ idx_zero symbol symbol_map idx_map cc S0)) by (rewrite Hhc; reflexivity).
          rewrite HS1snd. apply (hash_clause_preserves_wf Hlts Hltt cc S0 Hwf0). }
        pose proof (hash_clause_sets cc S0) as Hsets.
        assert (Hi_eq : i = fst (hash_clause idx idx_succ idx_zero symbol symbol_map idx_map cc S0)) by (rewrite Hhc; reflexivity).
        assert (HS1snd2 : S1 = snd (hash_clause idx idx_succ idx_zero symbol symbol_map idx_map cc S0)) by (rewrite Hhc; reflexivity).
        rewrite <- HS1snd2, <- Hi_eq in Hsets.
        assert (Hentry_S2 : qc_entry S2 (atom_fn cc) i (atom_args cc, atom_ret cc)).
        { assert (HS2eq : S2 = snd (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) rest S1)) by (rewrite Hrec; reflexivity).
          rewrite HS2eq.
          exact (proj2 (list_Mmap_qc_preserves
            (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs)
            (compile_query_clause_preserves_wf Hlts Hltt qvs)
            (compile_query_clause_mono Hlti qvs)
            rest S1 Hwf_S1) (atom_fn cc) i _ Hsets). }
        cbn [atom_fn] in Hentry_S2.
        assert (Hentry_Qfin : qc_entry Qfin f i (atom_args cc, atom_ret cc)).
        { apply Hmono'. rewrite Hrec. cbn [snd]. exact Hentry_S2. }
        assert (Hcvars : clause_vars = filter (fun x => inb x (out :: args)) qvs).
        { unfold clause_vars, sort_by_position_in. reflexivity. }
        assert (Hout_in_qvs : In out qvs).
        { apply (Hsub {| atom_fn := f; atom_args := args; atom_ret := out |}).
          { left. reflexivity. }
          { left. reflexivity. } }
        assert (Hout_in_cv : In out clause_vars).
        { rewrite Hcvars. apply filter_In. split.
          { exact Hout_in_qvs. }
          { apply Is_true_implies_eq_true.
            apply (proj2 (@inb_is_In idx Eqb_idx Eqb_idx_ok out (out :: args))).
            left. reflexivity. } }
        assert (Hcv_nonempty : 0 < length clause_vars).
        { destruct clause_vars as [|? ?].
          { destruct Hout_in_cv. }
          { apply PeanoNat.Nat.lt_0_succ. } }
        assert (Hbounds_args : forall t, In t (atom_args cc) -> t < length clause_vars).
        { intros t Ht_in.
          cbn [atom_args] in Ht_in.
          apply in_map_iff in Ht_in.
          destruct Ht_in as (arg_i & Hlookup & Harg_in).
          subst t. unfold sub.
          apply named_list_lookup_combine_seq_lt.
          assert (Harg_in_cv : In arg_i clause_vars).
          { rewrite Hcvars. apply filter_In. split.
            { apply (Hsub {| atom_fn := f; atom_args := args; atom_ret := out |}).
              { left. reflexivity. }
              { right. exact Harg_in. } }
            { apply Is_true_implies_eq_true.
              apply (proj2 (@inb_is_In idx Eqb_idx Eqb_idx_ok arg_i (out :: args))).
              right. exact Harg_in. } }
          destruct clause_vars as [|? ?].
          { destruct Harg_in_cv. }
          { apply PeanoNat.Nat.lt_0_succ. } }
        assert (Hbound_ret : (atom_ret cc) < length clause_vars).
        { cbn [atom_ret]. unfold sub. apply named_list_lookup_combine_seq_lt. exact Hcv_nonempty. }
        exists (atom_args cc), (atom_ret cc).
        exact (conj Hentry_Qfin (conj (ex_intro _ _ Hcvars) (conj Hbounds_args Hbound_ret))).
      + assert (Hrest_in : In (Build_erule_query_ptr idx symbol fsym nptr cvars)
                              (fst (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) rest S1))).
        { rewrite Hrec. cbn [fst]. exact Hrest. }
        exact (IH (fun a' Hin' => Hsub a' (or_intror Hin')) S1 Hwf_S1_gen Qfin Hmono' fsym nptr cvars Hrest_in).
  Qed.

  (* ============================================================== *)
  (* Helper: query_clause_ptrs from compile_rule                     *)
  (* ============================================================== *)

  Lemma compile_rule_inl_clause_ptrs :
    forall rf r st0 er st1,
      compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf r st0 = (inl er, st1) ->
      let '(assumptions, _, _) :=
        QueryOpt.optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie r rf in
      let qvs := dedup (eqb (A:=idx)) (flat_map (QueryOpt.atom_fvs idx symbol) assumptions) in
      uncurry cons (query_clause_ptrs idx symbol er)
        = fst (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) assumptions st0).
  Proof.
    intros rf r st0 er st1 Hc.
    unfold compile_rule in Hc.
    destruct (QueryOpt.optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie r rf)
      as [ [assumptions catoms] ceqs ] eqn:Hopt.
    set (qvs := dedup (eqb (A:=idx)) (flat_map (atom_fvs idx symbol) assumptions)) in *.
    destruct (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) assumptions st0)
      as [qcls_ptrs st'] eqn:Hmap.
    cbn [Mbind StateMonad.state_monad] in Hc.
    rewrite Hmap in Hc.
    destruct qcls_ptrs as [| c cs].
    - cbn [Mret StateMonad.state_monad] in Hc. inversion Hc.
    - cbn [Mret StateMonad.state_monad] in Hc. inversion Hc; subst.
      cbn [query_clause_ptrs uncurry].
      rewrite Hmap. cbn [fst]. reflexivity.
  Qed.

  (* ============================================================== *)
  (* C4: ptr-validity (run1iter_rule_hyps conjunct 4)               *)
  (* ============================================================== *)

  Lemma compiled_rules_ptr_valid
    (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
    (symbol_map_plus_ok : @map_plus_ok _ _ symbol_map_plus) :
    forall (rf : nat) (rules : list sequent) (er : erule idx symbol),
      In er (compiled_rules idx symbol symbol_map idx_map
               (build_rule_set idx_succ idx_zero rf rules)) ->
      forall fsym nptr cvars,
        In (Build_erule_query_ptr idx symbol fsym nptr cvars)
           (uncurry cons (query_clause_ptrs idx symbol er)) ->
        exists q_f cargs cv (Pf : idx -> bool),
          map.get (query_clauses idx symbol symbol_map idx_map
                     (build_rule_set idx_succ idx_zero rf rules)) fsym = Some q_f
          /\ map.get q_f nptr = Some (cargs, cv)
          /\ cvars = filter Pf (query_vars idx symbol er)
          /\ (forall t, In t cargs -> t < length cvars)
          /\ cv < length cvars.
  Proof.
    intros rf rules er Hin fsym nptr cvars Hptr.
    pose proof (in_compiled_rules_build_rule_set_mono Hlti Hlts Hltt rf rules er Hin)
      as (rule & st0 & st1 & Hrule_in & Hcompile & Hwf0 & Hmono_fin).
    destruct (list_Mmap (compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf) rules map.empty)
      as [crs cp] eqn:Hlm.
    set (Qfin := cp).
    assert (Hqc : query_clauses idx symbol symbol_map idx_map (build_rule_set idx_succ idx_zero rf rules) = map_map snd Qfin).
    { unfold build_rule_set. rewrite Hlm. destruct (split_sum_list crs). cbn [query_clauses]. reflexivity. }
    assert (Hmono_fin' : forall g j v, qc_entry st1 g j v -> qc_entry Qfin g j v).
    { intros g j v Hentry. exact (Hmono_fin g j v Hentry). }
    pose proof (compile_rule_inl_fields rf rule st0 er st1 Hcompile) as Hfields.
    destruct (QueryOpt.optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rule rf)
      as [ [assumptions catoms] ceqs ] eqn:Hopt.
    destruct Hfields as (Hqv & Hwc & Hwu).
    pose proof (compile_rule_inl_clause_ptrs rf rule st0 er st1 Hcompile) as Hptrs.
    rewrite Hopt in Hptrs. cbn [fst] in Hptrs.
    set (qvs := dedup (eqb (A:=idx)) (flat_map (atom_fvs idx symbol) assumptions)) in *.
    rewrite Hqv.
    assert (Hsub : forall b : Defs.atom idx symbol, In b assumptions ->
        forall x0, In x0 (Defs.atom_ret b :: Defs.atom_args b) -> In x0 qvs).
    { intros b Hbin x0 Hx0. unfold qvs.
      apply (proj1 (@dedup_preserves_In idx eqb (@eqb_boolspec idx Eqb_idx Eqb_idx_ok) (flat_map (atom_fvs idx symbol) assumptions) x0)).
      exact (proj2 (in_flat_map (atom_fvs idx symbol) assumptions x0) (ex_intro _ b (conj Hbin Hx0))). }
    assert (NDqvs : NoDup qvs).
    { unfold qvs. apply NoDup_dedup. }
    assert (Hmono_lm : forall g j v,
        qc_entry (snd (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) assumptions st0)) g j v ->
        qc_entry Qfin g j v).
    { intros g j v Hentry.
      apply Hmono_fin'.
      unfold compile_rule in Hcompile. rewrite Hopt in Hcompile. fold qvs in Hcompile.
      destruct (list_Mmap (compile_query_clause idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map qvs) assumptions st0) as [qcls_ptrs st'] eqn:Hmap.
      cbn [Mbind StateMonad.state_monad] in Hcompile. rewrite Hmap in Hcompile.
      destruct qcls_ptrs as [|c cs].
      { cbn [Mret StateMonad.state_monad] in Hcompile. inversion Hcompile. }
      cbn [Mret StateMonad.state_monad] in Hcompile. inversion Hcompile; subst.
      cbn [snd] in Hentry. exact Hentry. }
    rewrite Hptrs in Hptr.
    pose proof (list_Mmap_cqc_ptr_valid Hlti Hlts Hltt qvs NDqvs assumptions Hsub st0 Hwf0 Qfin Hmono_lm fsym nptr cvars Hptr)
      as (cargs & cv & Hqce & (Pf & HcvPf) & Hcargs_lt & Hcv_lt).
    destruct Hqce as (last & m & HgetQf & Hgetm).
    rewrite Hqc.
    refine (ex_intro _ m (ex_intro _ cargs (ex_intro _ cv (ex_intro _ Pf (conj _ (conj Hgetm (conj HcvPf (conj Hcargs_lt Hcv_lt)))))))).
    rewrite (@map_map_spec symbol symbol_map symbol_map_plus symbol_map_plus_ok
               (idx * idx_map (list nat * nat)) (idx_map (list nat * nat)) snd Qfin fsym).
    cbn [option_map].
    unfold Qfin in HgetQf. unfold Qfin.
    exact (eq_trans (f_equal (option_map snd) HgetQf) (eq_refl (Some m))).
  Qed.

  (* ============================================================== *)
  (* C5: query-var coverage (run1iter_rule_hyps conjunct 5)         *)
  (* ============================================================== *)

  Lemma compiled_rules_qvar_coverage
    (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
    (symbol_map_plus_ok : @map_plus_ok _ _ symbol_map_plus) :
    forall (rf : nat) (rules : list sequent) (er : erule idx symbol),
      In er (compiled_rules idx symbol symbol_map idx_map
               (build_rule_set idx_succ idx_zero rf rules)) ->
      forall x, In x (query_vars idx symbol er) ->
        exists a, In a (Semantics.query_atoms idx idx_zero symbol symbol_map idx_map
                          (query_clauses idx symbol symbol_map idx_map
                             (build_rule_set idx_succ idx_zero rf rules)) er)
               /\ In x (atom_ret a :: atom_args a).
  Proof.
    intros rf rules er Hin x Hx.
    pose proof (in_compiled_rules_build_rule_set_mono Hlti Hlts Hltt rf rules er Hin)
      as (rule & st0 & st1 & Hrule_in & Hcompile & Hwf0 & Hmono_fin).
    destruct (list_Mmap (compile_rule idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rf) rules map.empty)
      as [crs cp] eqn:Hlm.
    assert (Hmono_fin' : forall g j v, qc_entry st1 g j v -> qc_entry cp g j v).
    { intros g j v Hentry. exact (Hmono_fin g j v Hentry). }
    pose proof (compile_rule_inl_fields rf rule st0 er st1 Hcompile) as Hfields.
    destruct (QueryOpt.optimize_sequent' idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rule rf)
      as [ [assumptions catoms] ceqs ] eqn:Hopt.
    destruct Hfields as (Hqv & Hwc & Hwu).
    rewrite Hqv in Hx.
    apply (proj2 (@dedup_preserves_In idx eqb (@eqb_boolspec idx Eqb_idx Eqb_idx_ok) (flat_map (atom_fvs idx symbol) assumptions) x)) in Hx.
    apply (proj1 (in_flat_map (atom_fvs idx symbol) assumptions x)) in Hx.
    destruct Hx as (a & Ha_in & Hx_in_a).
    assert (Hqc : query_clauses idx symbol symbol_map idx_map (build_rule_set idx_succ idx_zero rf rules) = map_map snd cp).
    { unfold build_rule_set. rewrite Hlm. destruct (split_sum_list crs). cbn [query_clauses]. reflexivity. }
    pose proof (query_atoms_compile_rule_eq Hlti Hlts Hltt symbol_map_plus_ok rf rule st0 st1 er cp Hwf0 Hcompile Hmono_fin') as Hqa.
    rewrite Hopt in Hqa.
    rewrite Hqc. rewrite Hqa.
    exact (ex_intro _ a (conj Ha_in Hx_in_a)).
  Qed.

  (* ============================================================== *)
  (* C6: compiled_rules_run1iter_rule_hyps                           *)
  (* Bundle all 10 run1iter_rule_hyps conjuncts for build_rule_set   *)
  (* with conjuncts 9,10 taken as hypotheses.                        *)
  (* ============================================================== *)

  Lemma compiled_rules_run1iter_rule_hyps
    (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
    (symbol_map_plus_ok : @map_plus_ok _ _ symbol_map_plus)
    (spaced_list_intersect : forall B, WithDefault B -> (B -> B -> B) ->
          ne_list (idx_trie B * list bool) -> idx_trie B) :
    forall (m : model symbol) (Hm : Semantics.model_ok symbol m)
           (rf : nat) (rules : list sequent) (er : erule idx symbol)
           (e : instance),
      (forall rule, In rule rules ->
         model_satisfies_rule m (QueryOpt.optimize_sequent idx Eqb_idx idx_succ idx_zero symbol symbol_map idx_map idx_trie rule rf)) ->
      In er (compiled_rules idx symbol symbol_map idx_map (QueryOpt.build_rule_set idx_succ idx_zero rf rules)) ->
      (forall frontier_n sigma,
         In sigma (intersection_keys idx idx_trie spaced_list_intersect
                     (ne_map (trie_of_clause idx Eqb_idx symbol symbol_map idx_map idx_trie
                                (query_vars idx symbol er)
                                (fst (build_tries idx Eqb_idx symbol symbol_map symbol_map_plus
                                        idx_map idx_map_plus idx_trie unit
                                        (QueryOpt.build_rule_set idx_succ idx_zero rf rules) e))
                                frontier_n)
                             (query_clause_ptrs idx symbol er))) ->
         List.length (query_vars idx symbol er) = List.length sigma) ->
      (forall frontier_n sigma,
         In sigma (intersection_keys idx idx_trie spaced_list_intersect
                     (ne_map (trie_of_clause idx Eqb_idx symbol symbol_map idx_map idx_trie
                                (query_vars idx symbol er)
                                (fst (build_tries idx Eqb_idx symbol symbol_map symbol_map_plus
                                        idx_map idx_map_plus idx_trie unit
                                        (QueryOpt.build_rule_set idx_succ idx_zero rf rules) e))
                                frontier_n)
                             (query_clause_ptrs idx symbol er))) ->
         forall fsym nptr cvars,
         In (Build_erule_query_ptr idx symbol fsym nptr cvars)
            (uncurry cons (query_clause_ptrs idx symbol er)) ->
         map.get (fst (trie_of_clause idx Eqb_idx symbol symbol_map idx_map idx_trie
                         (query_vars idx symbol er)
                         (fst (build_tries idx Eqb_idx symbol symbol_map symbol_map_plus
                                 idx_map idx_map_plus idx_trie unit
                                 (QueryOpt.build_rule_set idx_succ idx_zero rf rules) e))
                         frontier_n
                         (Build_erule_query_ptr idx symbol fsym nptr cvars)))
                 (map fst (filter snd (combine sigma
                    (variable_flags idx Eqb_idx (query_vars idx symbol er) cvars))))
         = Some tt) ->
      SemanticsSaturate.run1iter_rule_hyps idx Eqb_idx idx_zero symbol symbol_map symbol_map_plus
        idx_map idx_map_plus idx_trie unit spaced_list_intersect m
        (QueryOpt.build_rule_set idx_succ idx_zero rf rules) e er.
  Proof.
    intros m Hm rf rules er e Hmsr Hin H9 H10.
    unfold SemanticsSaturate.run1iter_rule_hyps.
    cbn zeta.
    pose proof (in_compiled_rules_build_rule_set rf rules er Hin) as (rule & st0 & st1 & _ & Hc).
    repeat split.
    - exact (compile_rule_inl_NoDup_query_vars rf rule st0 er st1 Hc).
    - exact (compile_rule_inl_NoDup_write_vars rf rule st0 er st1 Hc).
    - exact (compiled_rules_erule_sound Hlti Hlts Hltt symbol_map_plus_ok m Hm rf rules er Hmsr Hin).
    - exact (compiled_rules_ptr_valid Hlti Hlts Hltt symbol_map_plus_ok rf rules er Hin).
    - exact (compiled_rules_qvar_coverage Hlti Hlts Hltt symbol_map_plus_ok rf rules er Hin).
    - exact (compile_rule_inl_write_query_disjoint rf rule st0 er st1 Hc).
    - exact (compile_rule_inl_write_clauses_cover rf rule st0 er st1 Hc).
    - exact (proj1 (compile_rule_inl_write_unifs_cover rf rule st0 er st1 Hc p H)).
    - exact (proj2 (compile_rule_inl_write_unifs_cover rf rule st0 er st1 Hc p H)).
    - exact H9.
    - exact H10.
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

  (* D0 domain converse: every key of [pullback_assignment a_opt sub] comes
     from some pair (x,y) in [sub] with [a_opt] defined at [y].  Stated with
     [In (x,y) sub] rather than the first-lookup image of [x], since on
     duplicate keys the head pair may [a_opt]-miss while a later occurrence
     supplies the value.  Used (with [clauses_to_instance_sub_in_domain] +
     uf id-freshness) to discharge domain-confinement of the pullback
     assignment [a_src] in [optimize_sequent_forward_atoms]. *)
  Lemma pullback_assignment_dom_converse {A} (a_opt : idx_map A)
        (sub : named_list idx idx) (x : idx) :
    Sep.has_key x (pullback_assignment a_opt sub) ->
    exists y, In (x, y) sub /\ Sep.has_key y a_opt.
  Proof.
    induction sub as [| [x0 y0] sub' IH]; intros Hhk.
    - cbn [pullback_assignment fold_right] in Hhk.
      unfold Sep.has_key in Hhk. rewrite map.get_empty in Hhk. destruct Hhk.
    - cbn [pullback_assignment fold_right] in Hhk.
      destruct (map.get a_opt y0) as [d|] eqn:Hy0.
      + (* head puts x0 -> d *)
        eqb_case x x0.
        * exists y0. split; [ left; reflexivity | ].
          unfold Sep.has_key; rewrite Hy0; exact I.
        * assert (Sep.has_key x (pullback_assignment a_opt sub')) as Hhk'.
          { unfold Sep.has_key in *. rewrite map.get_put_diff in Hhk by congruence.
            exact Hhk. }
          destruct (IH Hhk') as (y & Hin & Hhky).
          exists y. split; [ right; exact Hin | exact Hhky ].
      + (* head does nothing *)
        destruct (IH Hhk) as (y & Hin & Hhky).
        exists y. split; [ right; exact Hin | exact Hhky ].
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
    apply (SemanticsUtil.all_map_in (@atom_clause idx symbol)
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
    intros atoms Hfull a Hkeys Hconf Hass.
    (* Same forall_vars and same assumptions: just apply the hyp. *)
    specialize (Hfull a Hkeys Hconf Hass).
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
    intros a_opt Hkeys Hconf Hass; cbn -[map.tuples Properties.map.fold_empty] in *.
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

  (* ============================================================== *)
  (* next-monotonicity chain: clauses_to_instance_new_key_fresh      *)
  (* ============================================================== *)

  (* Order helpers on idx *)
  Definition idx_le (a b : idx) : Prop := a = b \/ lt a b.

  Lemma idx_le_refl (a : idx) : idx_le a a.
  Proof. left; reflexivity. Qed.

  Lemma idx_le_trans (Hltt : Transitive lt) (a b c : idx) :
    idx_le a b -> idx_le b c -> idx_le a c.
  Proof.
    intros [Hab | Hab] [Hbc | Hbc].
    - subst. left; reflexivity.
    - subst. right; exact Hbc.
    - subst. right; exact Hab.
    - right; exact (Hltt _ _ _ Hab Hbc).
  Qed.

  Lemma idx_le_succ (Hlts : forall x, lt x (idx_succ x)) (a : idx) :
    idx_le a (idx_succ a).
  Proof. right; apply Hlts. Qed.

  Lemma idx_le_not_lt (Hlti : Asymmetric lt) (a b : idx) :
    idx_le a b -> lt b a -> False.
  Proof.
    intros [Hab | Hab] Hba.
    - subst. exact (Hlti _ _ Hba Hba).
    - exact (Hlti _ _ Hab Hba).
  Qed.

  (* Primitive next facts *)

  (* alloc bumps next by one succ; the returned fresh id equals the old next *)
  Local Lemma alloc_next_succ
    (e : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    (equiv (snd (alloc idx idx_succ symbol symbol_map idx_map idx_trie unit e))).(next _ _ _)
    = idx_succ ((equiv e).(next _ _ _))
    /\ fst (alloc idx idx_succ symbol symbol_map idx_map idx_trie unit e)
       = (equiv e).(next _ _ _).
  Proof.
    unfold alloc.
    unfold UnionFind.alloc.
    destruct (equiv e) as [ra pa mr nx] eqn:Heqv.
    cbn. split; reflexivity.
  Qed.

  (* Defs.find preserves next *)
  Local Lemma Defs_find_next_preserved (x : idx)
    (e : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    (equiv (snd (Defs.find x e))).(next _ _ _)
    = (equiv e).(next _ _ _).
  Proof.
    unfold Defs.find.
    unfold UnionFind.find.
    destruct (equiv e) as [ra pa mr nx] eqn:Heqv.
    destruct (find_aux idx Eqb_idx (idx_map idx) (S mr) x pa) as [cx f] eqn:Hfa.
    cbn. reflexivity.
  Qed.

  (* UnionFind.union preserves next (via direct inspection of all branches) *)
  Local Lemma UnionFind_union_next_preserved
    (uf : union_find idx (idx_map idx) (idx_map nat)) (x y : idx) :
    (next _ _ _ (fst (UnionFind.union idx Eqb_idx (idx_map idx) (idx_map nat) uf x y)))
    = (next _ _ _ uf).
  Proof.
    unfold UnionFind.union.
    destruct uf as [ra pa mr nx] eqn:Huf.
    unfold UnionFind.find.
    destruct (find_aux idx Eqb_idx (idx_map idx) (S mr) x pa) as [cx f3] eqn:Hfa3.
    cbn [fst snd next rank parent max_rank].
    destruct (find_aux idx Eqb_idx (idx_map idx) (S mr) y f3) as [cy f4] eqn:Hfa4.
    cbn [fst snd next rank parent max_rank].
    eqb_case cx cy.
    { cbn [fst next]. reflexivity. }
    destruct (Nat.compare _ _);
      cbn [fst next]; reflexivity.
  Qed.

  (* Defs.union preserves next *)
  Local Lemma union_next_preserved (v v1 : idx)
    (e : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    (equiv (snd (Defs.union v v1 e))).(next _ _ _)
    = (equiv e).(next _ _ _).
  Proof.
    unfold Defs.union.
    cbn [Mbind StateMonad.state_monad Mret].
    destruct (Defs.find v e) as [cv e1] eqn:Hf1.
    cbn [fst snd].
    assert (Hn1 : (equiv e1).(next _ _ _) = (equiv e).(next _ _ _)).
    { pose proof (Defs_find_next_preserved v e) as H.
      rewrite Hf1 in H. cbn in H. exact H. }
    destruct (Defs.find v1 e1) as [cv1 e2] eqn:Hf2.
    cbn [fst snd].
    assert (Hn2 : (equiv e2).(next _ _ _) = (equiv e1).(next _ _ _)).
    { pose proof (Defs_find_next_preserved v1 e1) as H.
      rewrite Hf2 in H. cbn in H. exact H. }
    eqb_case cv cv1.
    { cbn [snd equiv]. congruence. }
    (* UnionFind.union preserves next *)
    pose proof (UnionFind_union_next_preserved (equiv e2) cv cv1) as Hn3.
    destruct (UnionFind.union idx Eqb_idx (idx_map idx) (idx_map nat) (equiv e2) cv cv1)
      as [uf' v'] eqn:Huu.
    cbn [fst] in Hn3.
    destruct (eqb cv v'); cbn [snd equiv next]; congruence.
  Qed.

  (* Helper: db_set doesn't change equiv (and thus next) *)
  Local Lemma db_set_next_preserved (a : atom)
    (e : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    (equiv (snd (Defs.db_set idx Eqb_idx symbol symbol_map idx_map idx_trie unit a e))).(next _ _ _)
    = (equiv e).(next _ _ _).
  Proof.
    unfold Defs.db_set.
    cbn [Mbind StateMonad.state_monad fst snd].
    unfold get_analyses.
    destruct (list_Mmap (get_analysis idx symbol symbol_map idx_map idx_trie unit)
                (atom_args a) e) as [arg_as e2] eqn:Hga.
    cbn [fst snd].
    destruct (Defs.update_analyses idx symbol symbol_map idx_map idx_trie unit
                (atom_ret a)
                (analyze idx symbol unit a arg_as) e2) as [pu e3] eqn:Hua.
    cbn [snd]. unfold db_set'. cbn [snd equiv next].
    unfold Defs.update_analyses in Hua. cbn [snd] in Hua. injection Hua as _ He3.
    subst e3.
    pose proof (list_Mmap_get_analysis_preserves_equiv_early (atom_args a) e) as Hea.
    rewrite Hga in Hea. cbn [snd] in Hea. rewrite <- Hea. reflexivity.
  Qed.

  (* update_entry preserves next (no allocation):
     union preserves next, db_set doesn't change equiv *)
  Local Lemma update_entry_next_preserved (a : atom)
    (e : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    (equiv (snd (update_entry a e))).(next _ _ _)
    = (equiv e).(next _ _ _).
  Proof.
    unfold update_entry. cbn [Mbind StateMonad.state_monad].
    destruct (Defs.db_lookup idx symbol symbol_map idx_map idx_trie unit
                (atom_fn a) (atom_args a) e) as [mout e'] eqn:Hlu.
    cbn [fst snd].
    assert (He' : e' = e).
    { unfold Defs.db_lookup in Hlu. cbn in Hlu. injection Hlu as _ <-. reflexivity. }
    subst e'. destruct mout as [r|].
    - (* Some r: union r (atom_ret a) *)
      cbn [Mseq Mbind Mret StateMonad.state_monad snd].
      destruct (@Defs.union idx Eqb_idx symbol symbol_map idx_map idx_trie unit _
                  r (atom_ret a) e) as [v_u e_u] eqn:Hu.
      cbn [snd].
      pose proof (union_next_preserved r (atom_ret a) e) as Hn.
      rewrite Hu in Hn. cbn [snd] in Hn. exact Hn.
    - (* None: db_set a *)
      cbn [Mret StateMonad.state_monad snd].
      exact (db_set_next_preserved a e).
  Qed.

  (* rename_lookup is next-monotone: on hit next unchanged, on miss next steps up by succ *)
  Local Lemma rename_lookup_next_invariant
    (Hlts : forall x, lt x (idx_succ x))
    (x : idx) (sub0 : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    let r := rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit
                x sub0 e0 in
    idx_le ((equiv e0).(next _ _ _)) ((equiv (snd r)).(next _ _ _))
    /\ (forall x' y', In (x', y') (snd (fst r)) ->
          In (x', y') sub0 \/ idx_le ((equiv e0).(next _ _ _)) y').
  Proof.
    unfold rename_lookup.
    destruct (named_list_lookup_err sub0 x) as [y|] eqn:Hlook.
    - (* hit: e unchanged, sub unchanged *)
      cbn [Mret StateMonad.state_monad fst snd].
      split.
      + apply idx_le_refl.
      + intros x' y' Hin. left. exact Hin.
    - (* miss: alloc *)
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
      cbn beta iota. unfold Basics.compose.
      destruct (alloc idx idx_succ symbol symbol_map idx_map idx_trie unit e0)
        as [fresh e1] eqn:Halloc.
      cbn [fst snd].
      pose proof (alloc_next_succ e0) as [Hn1 Hfresh].
      rewrite Halloc in Hn1, Hfresh. cbn [snd fst] in Hn1, Hfresh.
      split.
      + (* idx_le (next e0) (next e1) = idx_le (next e0) (succ (next e0)) *)
        rewrite Hn1. apply idx_le_succ. intros z; apply Hlts.
      + (* new sub = (x, fresh) :: sub0 *)
        intros x' y' Hin.
        cbn [map fst] in Hin.
        destruct Hin as [Heq | Hin].
        * (* (x', y') = (x, fresh) *)
          injection Heq as <- <-.
          right.
          (* fresh = next e0, idx_le (next e0) (next e0) *)
          rewrite <- Hfresh. apply idx_le_refl.
        * left. exact Hin.
  Qed.

  Local Lemma list_Mmap_rename_lookup_next_invariant
    (Hlts : forall x, lt x (idx_succ x))
    (Hltt : Transitive lt)
    (args : list idx) :
    forall (sub0 : named_list idx idx)
      (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit),
    let r := list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                          idx_trie unit) args sub0 e0 in
    idx_le ((equiv e0).(next _ _ _)) ((equiv (snd r)).(next _ _ _))
    /\ (forall x' y', In (x', y') (snd (fst r)) ->
          In (x', y') sub0 \/ idx_le ((equiv e0).(next _ _ _)) y').
  Proof.
    induction args as [|a args IH]; intros sub0 e0.
    - cbn. split.
      + apply idx_le_refl.
      + intros x' y' Hin. left. exact Hin.
    - cbn [list_Mmap].
      destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                  unit a sub0 e0) as [ [a' sub1] e1 ] eqn:Hrla.
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
      cbn beta iota. unfold Basics.compose.
      rewrite Hrla. cbn [fst snd uncurry].
      pose proof (rename_lookup_next_invariant Hlts a sub0 e0) as [Hle1 Hsub1].
      rewrite Hrla in Hle1, Hsub1. cbn [fst snd] in Hle1, Hsub1.
      pose proof (IH sub1 e1) as [Hle2 Hsub2].
      destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                             idx_trie unit) args sub1 e1) as [ [args2 sub3] e3 ] eqn:Hq.
      cbn [fst snd] in Hle2, Hsub2 |- *.
      split.
      + exact (idx_le_trans Hltt _ _ _ Hle1 Hle2).
      + intros x' y' Hin.
        specialize (Hsub2 x' y' Hin).
        destruct Hsub2 as [Hin_sub1 | Hle_y'].
        * specialize (Hsub1 x' y' Hin_sub1).
          destruct Hsub1 as [Hs0 | Hle_y''].
          -- left; exact Hs0.
          -- right; exact Hle_y''.
        * right; exact (idx_le_trans Hltt _ _ _ Hle1 Hle_y').
  Qed.

  Local Lemma rename_atom_next_invariant
    (Hlts : forall x, lt x (idx_succ x))
    (Hltt : Transitive lt)
    (a : atom) (sub0 : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    let r := rename_atom idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie unit
               a sub0 e0 in
    idx_le ((equiv e0).(next _ _ _)) ((equiv (snd r)).(next _ _ _))
    /\ (forall x' y', In (x', y') (snd (fst r)) ->
          In (x', y') sub0 \/ idx_le ((equiv e0).(next _ _ _)) y').
  Proof.
    destruct a as [f args out].
    unfold rename_atom. cbn [atom_fn atom_args atom_ret].
    cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
    cbn beta iota. unfold Basics.compose.
    pose proof (list_Mmap_rename_lookup_next_invariant Hlts Hltt args sub0 e0) as [Hle1 Hsub1].
    set (LM := list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                            idx_trie unit) args sub0 e0) in *.
    destruct LM as [ [args' sub1] e1 ] eqn:Hq1.
    cbn [fst snd] in Hle1, Hsub1.
    cbn [fst snd uncurry].
    destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                unit out sub1 e1) as [ [out' sub2] e2 ] eqn:Hq2.
    cbn [fst snd uncurry].
    pose proof (rename_lookup_next_invariant Hlts out sub1 e1) as [Hle2 Hsub2].
    rewrite Hq2 in Hle2, Hsub2. cbn [fst snd] in Hle2, Hsub2.
    split.
    - exact (idx_le_trans Hltt _ _ _ Hle1 Hle2).
    - intros x' y' Hin.
      specialize (Hsub2 x' y' Hin).
      destruct Hsub2 as [Hin_sub1 | Hle_y'].
      + specialize (Hsub1 x' y' Hin_sub1).
        destruct Hsub1 as [Hs0 | Hle_y''].
        * left; exact Hs0.
        * right; exact Hle_y''.
      + right; exact (idx_le_trans Hltt _ _ _ Hle1 Hle_y').
  Qed.

  Local Lemma add_clause_to_instance_next_invariant
    (Hlts : forall x, lt x (idx_succ x))
    (Hltt : Transitive lt)
    (c : Semantics.clause idx symbol) (sub0 : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    let r := add_clause_to_instance idx Eqb_idx idx_succ symbol symbol_map idx_map
                idx_trie unit c sub0 e0 in
    idx_le ((equiv e0).(next _ _ _)) ((equiv (snd r)).(next _ _ _))
    /\ (forall x' y', In (x', y') (snd (fst r)) ->
          In (x', y') sub0 \/ idx_le ((equiv e0).(next _ _ _)) y').
  Proof.
    destruct c as [xx yy | a_clause].
    - (* eq_clause xx yy *)
      unfold add_clause_to_instance.
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
      cbn beta iota. unfold Basics.compose.
      destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                  unit xx sub0 e0) as [ [x' sub1] e1 ] eqn:Hrx.
      cbn [fst snd uncurry].
      destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                  unit yy sub1 e1) as [ [y' sub2] e2 ] eqn:Hry.
      cbn [fst snd uncurry].
      cbn [lift StateMonad.state_monad Mbind Mret fst snd].
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mseq Mbind Mret].
      cbn beta iota. unfold Basics.compose.
      destruct (Defs.union x' y' e2) as [v e3] eqn:Hu.
      cbn [uncurry fst snd].
      pose proof (rename_lookup_next_invariant Hlts xx sub0 e0) as [Hle1 Hsub1].
      rewrite Hrx in Hle1, Hsub1. cbn [fst snd] in Hle1, Hsub1.
      pose proof (rename_lookup_next_invariant Hlts yy sub1 e1) as [Hle2 Hsub2].
      rewrite Hry in Hle2, Hsub2. cbn [fst snd] in Hle2, Hsub2.
      pose proof (union_next_preserved x' y' e2) as Hle3.
      rewrite Hu in Hle3. cbn [snd] in Hle3.
      split.
      + apply (idx_le_trans Hltt _ _ _ Hle1).
        apply (idx_le_trans Hltt _ _ _ Hle2).
        rewrite Hle3. apply idx_le_refl.
      + intros x'' y'' Hin.
        specialize (Hsub2 x'' y'' Hin).
        destruct Hsub2 as [Hin_sub1 | Hle_y''].
        * specialize (Hsub1 x'' y'' Hin_sub1).
          destruct Hsub1 as [Hs0 | Hle_y'''].
          -- left; exact Hs0.
          -- right; exact Hle_y'''.
        * right; exact (idx_le_trans Hltt _ _ _ Hle1 Hle_y'').
    - (* atom_clause a_clause *)
      unfold add_clause_to_instance.
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind].
      cbn beta iota. unfold Basics.compose.
      destruct (rename_atom idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                  unit a_clause sub0 e0) as [ [a' sub1] e1 ] eqn:Hra.
      cbn [fst snd uncurry].
      cbn [lift StateMonad.state_monad Mbind Mret fst snd].
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mseq Mbind Mret].
      cbn beta iota. unfold Basics.compose.
      destruct (update_entry a' e1) as [u e2] eqn:Hue.
      cbn [uncurry fst snd].
      pose proof (rename_atom_next_invariant Hlts Hltt a_clause sub0 e0) as [Hle1 Hsub1].
      rewrite Hra in Hle1, Hsub1. cbn [fst snd] in Hle1, Hsub1.
      pose proof (update_entry_next_preserved a' e1) as Hue2.
      rewrite Hue in Hue2. cbn [snd] in Hue2.
      split.
      + apply (idx_le_trans Hltt _ _ _ Hle1).
        rewrite Hue2. apply idx_le_refl.
      + intros x' y' Hin.
        specialize (Hsub1 x' y' Hin).
        destruct Hsub1 as [Hs0 | Hle_y'].
        * left; exact Hs0.
        * right; exact Hle_y'.
  Qed.

  Local Lemma clauses_to_instance_next_invariant
    (Hlts : forall x, lt x (idx_succ x))
    (Hltt : Transitive lt)
    (cs : list (Semantics.clause idx symbol))
    (sub0 : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit) :
    match clauses_to_instance idx_succ (analysis_result:=unit) cs sub0 e0 with
    | (_, sub1, e1) =>
        idx_le ((equiv e0).(next _ _ _)) ((equiv e1).(next _ _ _))
        /\ (forall x y, In (x, y) sub1 ->
              In (x, y) sub0 \/ idx_le ((equiv e0).(next _ _ _)) y)
    end.
  Proof.
    revert sub0 e0.
    induction cs as [|c cs IH]; intros sub0 e0.
    - cbn. split.
      + apply idx_le_refl.
      + intros x y Hin. left. exact Hin.
    - cbn [Semantics.clauses_to_instance list_Miter].
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mseq Mbind Mret].
      cbn beta iota. unfold Basics.compose.
      destruct (add_clause_to_instance idx Eqb_idx idx_succ symbol symbol_map idx_map
                  idx_trie unit c sub0 e0) as [q e1] eqn:Hadd.
      destruct q as [u sub_step].
      cbn [snd uncurry].
      pose proof (add_clause_to_instance_next_invariant Hlts Hltt c sub0 e0) as [Hle1 Hsub_step].
      rewrite Hadd in Hle1, Hsub_step. cbn [fst snd] in Hle1, Hsub_step.
      pose proof (IH sub_step e1) as IHc.
      destruct (clauses_to_instance idx_succ (analysis_result:=unit) cs sub_step e1)
        as [ [u2 sub_final] e_final] eqn:Hctc.
      cbn [snd fst] in IHc |- *.
      destruct IHc as [Hle2 Hsub_final].
      split.
      + exact (idx_le_trans Hltt _ _ _ Hle1 Hle2).
      + intros x y Hxy.
        specialize (Hsub_final x y Hxy).
        destruct Hsub_final as [Hin_step | Hle_y].
        * specialize (Hsub_step x y Hin_step).
          destruct Hsub_step as [Hs0 | Hle_y'].
          -- left; exact Hs0.
          -- right; exact Hle_y'.
        * right; exact (idx_le_trans Hltt _ _ _ Hle1 Hle_y).
  Qed.

  (* F5': every new egraph id introduced by clauses_to_instance is strictly
     above all pre-existing keys in the union-find's parent map.
     This means it cannot collide with any id already allocated in e0. *)
  Lemma clauses_to_instance_new_key_fresh
    (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x)) (Hltt : Transitive lt)
    (cs : list (Semantics.clause idx symbol))
    (sub0 : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit)
    (x y : idx) :
    (exists roots, UnionFind.union_find_ok lt (equiv e0) roots) ->
    match clauses_to_instance idx_succ (analysis_result:=unit) cs sub0 e0 with
    | (_, sub1, _) =>
        In (x, y) sub1 ->
        ~ In x (map fst sub0) ->
        ~ Sep.has_key y (parent (equiv e0))
    end.
  Proof.
    intros [roots Hok].
    pose proof (clauses_to_instance_next_invariant Hlts Hltt cs sub0 e0) as Hinv.
    destruct (clauses_to_instance idx_succ (analysis_result:=unit) cs sub0 e0)
      as [ [u sub1] e1] eqn:Hctc.
    cbn [fst snd] in Hinv |- *.
    destruct Hinv as [_ Hsub1].
    intros Hxy Hnotin Hhk.
    specialize (Hsub1 x y Hxy).
    destruct Hsub1 as [Hinsub0 | Hle].
    - (* (x, y) in sub0 => x in dom(sub0) => contradicts Hnotin *)
      exact (Hnotin (in_map fst sub0 (x, y) Hinsub0)).
    - (* idx_le (next e0) y, and has_key y (parent (equiv e0)) *)
      (* by next_upper_bound: lt y (next e0) *)
      pose proof (@UnionFind.next_upper_bound _ _ _ lt _ _ Hok y) as Hub.
      unfold Sep.has_key in Hhk.
      destruct (map.get (parent (equiv e0)) y) as [p|] eqn:Hgy;
        [|destruct Hhk].
      unfold Sep.has_key in Hub.
      rewrite Hgy in Hub.
      exact (idx_le_not_lt Hlti _ _ Hle (Hub I)).
  Qed.

  (* sub_in_domain helpers: every new key added by the renaming primitives
     is contained in the source vars touched by that primitive. *)

  Local Lemma rename_lookup_sub_in_domain
    (xv : idx) (sub0' : named_list idx idx)
    (e0' : Defs.instance idx symbol symbol_map idx_map idx_trie unit)
    (k : idx) :
    In k (map fst (snd (fst (rename_lookup idx Eqb_idx idx_succ symbol symbol_map
                              idx_map idx_trie unit xv sub0' e0')))) ->
    In k (map fst sub0') \/ k = xv.
  Proof.
    intros Hin. unfold rename_lookup in Hin.
    destruct (named_list_lookup_err sub0' xv) as [yv|] eqn:Hlook.
    - cbn [Mret StateMonad.state_monad fst snd] in Hin. left. exact Hin.
    - cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind] in Hin.
      cbn beta iota in Hin. unfold Basics.compose in Hin.
      destruct (alloc idx idx_succ symbol symbol_map idx_map idx_trie unit e0')
        as [fresh e1] eqn:Halloc.
      cbn [fst snd] in Hin. cbn [map fst] in Hin.
      destruct Hin as [Heq | Hin]; [ right; symmetry; exact Heq | left; exact Hin ].
  Qed.

  Local Lemma list_Mmap_rename_lookup_sub_in_domain (args : list idx) :
    forall (sub0' : named_list idx idx)
      (e0' : Defs.instance idx symbol symbol_map idx_map idx_trie unit)
      (k : idx),
    In k (map fst (snd (fst (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol
                              symbol_map idx_map idx_trie unit) args sub0' e0')))) ->
    In k (map fst sub0') \/ In k args.
  Proof.
    induction args as [|a args IH]; intros sub0' e0' k Hin.
    - cbn in Hin. left. exact Hin.
    - cbn [list_Mmap] in Hin.
      destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                  unit a sub0' e0') as [p e1] eqn:Hrla.
      destruct p as [a' sub1].
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind] in Hin.
      cbn beta iota in Hin. unfold Basics.compose in Hin.
      rewrite Hrla in Hin. cbn [fst snd uncurry] in Hin.
      pose proof (IH sub1 e1 k) as HIH.
      destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                             idx_trie unit) args sub1 e1) as [ [args2 sub3] e3 ] eqn:Hq.
      cbn [fst snd uncurry] in Hin, HIH.
      specialize (HIH Hin).
      destruct HIH as [Hsub1 | Hargs].
      + pose proof (rename_lookup_sub_in_domain a sub0' e0' k) as Hrl.
        rewrite Hrla in Hrl. cbn [fst snd] in Hrl.
        specialize (Hrl Hsub1).
        destruct Hrl as [Hs0 | Hka];
          [ left; exact Hs0 | right; left; symmetry; exact Hka ].
      + right; right; exact Hargs.
  Qed.

  Local Lemma rename_atom_sub_in_domain
    (a : atom) (sub0' : named_list idx idx)
    (e0' : Defs.instance idx symbol symbol_map idx_map idx_trie unit)
    (k : idx) :
    In k (map fst (snd (fst (rename_atom idx Eqb_idx idx_succ symbol symbol_map
                              idx_map idx_trie unit a sub0' e0')))) ->
    In k (map fst sub0') \/ In k (atom_ret a :: atom_args a).
  Proof.
    intros Hin. destruct a as [f args out].
    unfold rename_atom in Hin. cbn [atom_fn atom_args atom_ret] in Hin |- *.
    cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind] in Hin.
    cbn beta iota in Hin. unfold Basics.compose in Hin.
    destruct (list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                           idx_trie unit) args sub0' e0') as [ [args' sub1] e1 ] eqn:Hq1.
    cbn [fst snd uncurry] in Hin.
    destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                unit out sub1 e1) as [ [ret' sub2] e2 ] eqn:Hq2.
    cbn [fst snd uncurry] in Hin.
    pose proof (rename_lookup_sub_in_domain out sub1 e1 k) as Hrl.
    rewrite Hq2 in Hrl. cbn [fst snd] in Hrl.
    specialize (Hrl Hin).
    destruct Hrl as [Hsub1 | Hkout].
    - pose proof (list_Mmap_rename_lookup_sub_in_domain args sub0' e0' k) as Hlm.
      set (LM := list_Mmap (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map
                              idx_trie unit) args sub0' e0') in *.
      rewrite Hq1 in Hlm. cbn [fst snd] in Hlm.
      specialize (Hlm Hsub1).
      destruct Hlm as [Hs0 | Hargs];
        [ left; exact Hs0 | right; right; exact Hargs ].
    - right; left; symmetry; exact Hkout.
  Qed.

  Local Lemma add_clause_to_instance_sub_in_domain
    (c : Semantics.clause idx symbol) (sub0' : named_list idx idx)
    (e0' : Defs.instance idx symbol symbol_map idx_map idx_trie unit)
    (k : idx) :
    In k (map fst (snd (fst (add_clause_to_instance idx Eqb_idx idx_succ symbol
                              symbol_map idx_map idx_trie unit c sub0' e0')))) ->
    In k (map fst sub0') \/ In k (clause_vars idx symbol c).
  Proof.
    intros Hin. destruct c as [xx yy | a_clause].
    - (* eq_clause xx yy *)
      cbn [clause_vars]. unfold add_clause_to_instance in Hin.
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind] in Hin.
      cbn beta iota in Hin. unfold Basics.compose in Hin.
      destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                  unit xx sub0' e0') as [ [x' sub1'] e1' ] eqn:Hrx.
      cbn [fst snd uncurry] in Hin.
      destruct (rename_lookup idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                  unit yy sub1' e1') as [ [y' sub2'] e2' ] eqn:Hry.
      cbn [fst snd uncurry] in Hin.
      cbn [lift StateMonad.state_monad Mbind Mret fst snd] in Hin.
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mseq Mbind Mret] in Hin.
      cbn beta iota in Hin. unfold Basics.compose in Hin.
      destruct (Defs.union x' y' e2') as [v e3'] eqn:Hu.
      cbn [uncurry fst snd] in Hin.
      pose proof (rename_lookup_sub_in_domain yy sub1' e1' k) as Hry2.
      rewrite Hry in Hry2. cbn [fst snd] in Hry2. specialize (Hry2 Hin).
      destruct Hry2 as [Hsub1' | Hkyy].
      + pose proof (rename_lookup_sub_in_domain xx sub0' e0' k) as Hrx2.
        rewrite Hrx in Hrx2. cbn [fst snd] in Hrx2. specialize (Hrx2 Hsub1').
        destruct Hrx2 as [Hs0 | Hkxx];
          [ left; exact Hs0 | right; left; symmetry; exact Hkxx ].
      + right; right; left; symmetry; exact Hkyy.
    - (* atom_clause a_clause *)
      cbn [clause_vars]. unfold add_clause_to_instance in Hin.
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mret Mbind] in Hin.
      cbn beta iota in Hin. unfold Basics.compose in Hin.
      destruct (rename_atom idx Eqb_idx idx_succ symbol symbol_map idx_map idx_trie
                  unit a_clause sub0' e0') as [ [a' sub1'] e1' ] eqn:Hra.
      cbn [fst snd uncurry] in Hin.
      cbn [lift StateMonad.state_monad Mbind Mret fst snd] in Hin.
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mseq Mbind Mret] in Hin.
      cbn beta iota in Hin. unfold Basics.compose in Hin.
      destruct (update_entry a' e1') as [u' e2'] eqn:Hue.
      cbn [uncurry fst snd] in Hin.
      pose proof (rename_atom_sub_in_domain a_clause sub0' e0' k) as Hra2.
      rewrite Hra in Hra2. cbn [fst snd] in Hra2. specialize (Hra2 Hin). exact Hra2.
  Qed.

  (* Every key in the renaming produced by [clauses_to_instance] is either
     a key of the initial renaming or a variable of one of the clauses.
     Used to show the renaming's domain is contained in the source vars. *)
  Lemma clauses_to_instance_sub_in_domain
    (cs : list (Semantics.clause idx symbol))
    (sub0 : named_list idx idx)
    (e0 : Defs.instance idx symbol symbol_map idx_map idx_trie unit)
    (x y : idx) :
    match clauses_to_instance idx_succ (analysis_result:=unit) cs sub0 e0 with
    | (_, sub1, _) =>
        In (x, y) sub1 ->
        In x (map fst sub0) \/ In x (flat_map (clause_vars idx symbol) cs)
    end.
  Proof.
    revert sub0 e0.
    induction cs as [|c cs IH]; intros sub0 e0.
    - cbn. intros Hxy. left. exact (in_map fst sub0 (x,y) Hxy).
    - cbn [Semantics.clauses_to_instance list_Miter].
      cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mseq Mbind Mret].
      cbn beta iota. unfold Basics.compose.
      destruct (add_clause_to_instance idx Eqb_idx idx_succ symbol symbol_map idx_map
                  idx_trie unit c sub0 e0) as [q e1] eqn:Hadd.
      destruct q as [u sub_step].
      cbn [snd uncurry].
      pose proof (IH sub_step e1) as IHc.
      destruct (clauses_to_instance idx_succ (analysis_result:=unit) cs sub_step e1)
        as [ [u2 sub_final] e_final] eqn:Hctc.
      cbn [snd fst] in IHc |- *.
      intros Hxy. specialize (IHc Hxy).
      cbn [flat_map].
      destruct IHc as [Hstep | Htail].
      + pose proof (add_clause_to_instance_sub_in_domain c sub0 e0 x) as Hac.
        rewrite Hadd in Hac. cbn [fst snd] in Hac. specialize (Hac Hstep).
        destruct Hac as [Hs0 | Hcv];
          [ left; exact Hs0 | right; apply in_or_app; left; exact Hcv ].
      + right; apply in_or_app; right; exact Htail.
  Qed.

  (* Specialized sibling of [optimize_sequent_forward] for the atom-only,
     hash-consed assumptions produced by [rule_to_log_rule].  This is the
     form consumed on the egraph_sound path (Phase 6 / schedule_sound).

     Proof strategy ("Route 2", see project-optimize-sequent-forward memo):
     reduce the [optimize_sequent] pipeline to named egraphs
     (e_assum / e_c2), build the STRONG pullback assignment
     [a_src := pullback_assignment a_opt sub2] that pulls back EVERY
     conclusion id through [a_opt], feed it through the source rule's
     satisfaction ([Hsat]), then push the conclusions forward through
     [clauses_to_instance]/rebuild/force_equiv via the strengthened
     [clauses_to_instance_preserves_ok] (renaming-consistency + domain-bound
     conjuncts), reading the optimized conclusion atoms/eqs back with
     [db_to_atoms_sound]/[uf_eqs_sound] + [incl_remove_atoms]/[filter] subset.
     The final witness [map.putmany i_c a_opt] overrides with [a_opt] on the
     assumption ids (they agree by the renaming consistency) and equals the
     conclusion interpretation [i_c] elsewhere. *)
  (* Parametric in the rebuild fuel [rf]: the proof treats the fuel opaquely
     (it only ever feeds [rf] to [rebuild]/[rebuild_sound], both of which hold
     for any fuel), so soundness of the optimized sequent holds at EVERY fuel —
     not just the [var_count^2] baked into the [optimize_sequent] notation.
     This lets the bridge instantiate at the consumer's arbitrary [rebuild_fuel]
     (Automation.v), matching the fuel [compile_rule]/[build_rule_set] uses. *)
  Lemma optimize_sequent_forward_atoms
        (s : sequent) (rf : nat) (m : model symbol) (Hm : model_ok symbol m)
        (Hlti : Asymmetric lt) (Hlts : forall x, lt x (idx_succ x))
        (Hltt : Transitive lt)
        (atoms : list atom)
        (Hassum : s.(seq_assumptions) = map atom_clause atoms)
        (Huniq : NoDup (map (fun a => (atom_fn a, atom_args a)) atoms)) :
    model_satisfies_rule m s ->
    model_satisfies_rule m
      (QueryOpt.optimize_sequent idx Eqb_idx idx_succ idx_zero
         symbol symbol_map idx_map idx_trie s rf).
  Proof.
    intros Hsat. unfold model_satisfies_rule. intros a_opt Hkeys Hconf Hass.
    set (RFUEL := rf) in *.
    unfold QueryOpt.optimize_sequent in Hkeys, Hconf, Hass |- *.
    unfold sequent_of_states_seq in Hkeys, Hconf, Hass |- *.
    cbn [seq_assumptions seq_conclusions] in Hkeys, Hconf, Hass |- *.
    (* Reduce the state-monad pipeline to named egraphs. *)
    rewrite Hassum in Hkeys, Hconf, Hass |- *.
    cbv delta [StateMonad.state_monad transformer_monad stateT_trans Mseq Mbind Mret lift Basics.compose]
      in Hkeys, Hconf, Hass |- *.
    cbn beta iota in Hkeys, Hconf, Hass |- *.
    destruct (clauses_to_instance idx_succ (analysis_result:=unit) (map atom_clause atoms) []
                (empty_egraph idx_zero unit)) as [ [u1 sub1] e1] eqn:Hcti_a.
    destruct (rebuild RFUEL e1) as [u2 e_assum] eqn:Hrb_a.
    cbn beta iota in Hkeys, Hconf, Hass |- *.
    cbn [snd fst uncurry] in Hkeys, Hconf, Hass |- *.
    destruct (clauses_to_instance idx_succ (analysis_result:=unit) (seq_conclusions s) sub1 e_assum)
      as [ [u3 sub2] e_c0] eqn:Hcti_c.
    cbn beta iota in Hkeys, Hconf, Hass |- *.
    destruct (rebuild RFUEL e_c0) as [u4 e_c1] eqn:Hrb_c.
    destruct (force_equiv idx Eqb_idx symbol symbol_map idx_map idx_trie (X:=unit) e_c1)
      as [u5 e_c2] eqn:Hfe_c.
    cbn beta iota in Hkeys, Hconf, Hass |- *.
    cbn [snd] in Hkeys, Hconf, Hass |- *.
    set (AA := db_to_atoms (db e_assum)) in *.
    set (CE := map.tuples (parent (equiv e_c2))) in *.
    match goal with |- context[db_to_atoms (db (snd ?L))] =>
      set (CD := db_to_atoms (db (snd L))) in * end.
    (* Step 1: no-collision facts on the assumption pass; renamed atoms
       survive rebuild into e_assum. *)
    pose proof (clauses_to_instance_atoms_no_collision Hlti Hlts Hltt atoms Huniq) as Hnc.
    rewrite Hcti_a in Hnc.
    destruct Hnc as (Hwl_e1 & Hren_e1_db & Hvars_sub1).
    pose proof (@Semantics.rebuild_preserves_atom_in_db idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero
       symbol Eqb_symbol Eqb_symbol_ok symbol_map symbol_map_ok idx_map idx_trie idx_trie_ok unit _ RFUEL) as Hrp.
    unfold vc in Hrp. specialize (Hrp e1). rewrite Hrb_a in Hrp. cbn [snd] in Hrp.
    specialize (Hrp Hwl_e1). destruct Hrp as [Hdb_iff Hwl_assum].
    assert (Hren_assum_db : forall a, In a atoms ->
      atom_in_db (Build_atom (atom_fn a) (map (named_list_lookup default sub1) (atom_args a))
        (named_list_lookup default sub1 (atom_ret a))) (db e_assum))
      by (intros a Ha; apply (proj2 (Hdb_iff _)); apply Hren_e1_db; exact Ha).
    (* Step 2: sub2 extends sub1; lift the renamed atoms / vars facts to sub2;
       define the strong pullback assignment and prove it sound on source assumptions. *)
    assert (Hsub_mono : forall z w, named_list_lookup_err sub1 z = Some w ->
       named_list_lookup_err sub2 z = Some w)
      by (intros z w Hzw;
          pose proof (clauses_to_instance_sub_mono (seq_conclusions s) sub1 e_assum z w Hzw) as Hmm;
          rewrite Hcti_c in Hmm; exact Hmm).
    assert (Hvars_sub2 : forall a, In a atoms -> forall x, In x (atom_ret a :: atom_args a) ->
       exists y, named_list_lookup_err sub2 x = Some y)
      by (intros a Ha x Hx; destruct (Hvars_sub1 a Ha x Hx) as [y Hy]; exists y; apply Hsub_mono; exact Hy).
    assert (Hren_assum_db2 : forall a, In a atoms ->
      atom_in_db (Build_atom (atom_fn a) (map (named_list_lookup default sub2) (atom_args a))
        (named_list_lookup default sub2 (atom_ret a))) (db e_assum))
      by (intros a Ha;
          replace (map (named_list_lookup default sub2) (atom_args a))
            with (map (named_list_lookup default sub1) (atom_args a))
            by (apply map_lookup_default_ext;
                [ exact Hsub_mono | intros x Hx; exact (Hvars_sub1 a Ha x (or_intror Hx)) ]);
          replace (named_list_lookup default sub2 (atom_ret a))
            with (named_list_lookup default sub1 (atom_ret a))
            by (destruct (Hvars_sub1 a Ha (atom_ret a) (or_introl eq_refl)) as [yr Hyr];
                rewrite (named_list_lookup_err_to_lookup default sub1 (atom_ret a) yr Hyr);
                rewrite (named_list_lookup_err_to_lookup default sub2 (atom_ret a) yr (Hsub_mono _ _ Hyr));
                reflexivity);
          apply Hren_assum_db; exact Ha).
    set (a_src := pullback_assignment a_opt sub2).
    pose proof (a_src_sound_on_assumptions m Hm atoms sub2 a_opt e_assum Hvars_sub2 Hren_assum_db2 Hass)
      as Hsrc_assum.
    (* Step 4: build the interpretation i_e1 for the assumption pass from empty
       (handles any unions generically) and lift it to e_assum via rebuild. *)
    destruct (Semantics.empty_sound_for_interpretation idx lt idx_succ idx_zero symbol symbol_map
                symbol_map_ok idx_map idx_map_ok idx_trie unit m) as [Hok_empty Hsnd_empty].
    pose proof (clauses_to_instance_preserves_ok Hlti Hlts Hltt m Hm (map atom_clause atoms) []
       (empty_egraph idx_zero unit) (map.empty : idx_map (domain symbol m)) a_src
       Hok_empty Hsnd_empty
       ltac:(intros ? ? []) ltac:(intros ? ? []) Hsrc_assum) as Hpo_a.
    rewrite Hcti_a in Hpo_a.
    destruct Hpo_a as [Hok_e1 [i_e1 [Hext_e1 [Hsnd_e1 [Hren_e1 Hdom_e1] ] ] ] ].
    pose proof (@Semantics.rebuild_sound idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol Eqb_symbol Eqb_symbol_ok symbol_map symbol_map_ok idx_map idx_map_ok idx_trie idx_trie_ok unit _ m Hm (fun _ => True) RFUEL) as Hrs_a.
    unfold vc in Hrs_a. specialize (Hrs_a e1). rewrite Hrb_a in Hrs_a. cbn [snd] in Hrs_a.
    specialize (Hrs_a Hok_e1). destruct Hrs_a as [Hok_assum Hde_a].
    pose proof (proj1 (Hde_a i_e1) Hsnd_e1) as Hsnd_assum.
    (* a_src is defined on every source-assumption variable (needed for has_key). *)
    assert (Hkeys_src : forall x, In x (forall_vars s) -> Sep.has_key x a_src)
      by (intros x Hx;
          unfold forall_vars in Hx; rewrite Hassum in Hx;
          apply in_flat_map in Hx; destruct Hx as [c [Hc Hxc] ];
          apply in_map_iff in Hc; destruct Hc as [a0 [Hac Ha0] ]; subst c;
          cbn [clause_vars] in Hxc;
          pose proof (in_all (clause_sound_for_model idx symbol idx_map m a_src) _ _ Hsrc_assum
            (in_map (@atom_clause idx symbol) _ _ Ha0)) as Hsa;
          cbn [clause_sound_for_model] in Hsa;
          unfold Semantics.atom_sound_for_model in Hsa;
          destruct (list_Mmap (map.get a_src) (atom_args a0)) as [argv|] eqn:Hargv; [|cbn in Hsa; contradiction];
          destruct (map.get a_src (atom_ret a0)) as [retv|] eqn:Hretv; [|cbn in Hsa; contradiction];
          destruct Hxc as [Heq | Hin];
          [ subst x; unfold Sep.has_key; rewrite Hretv; exact I
          | destruct (SemanticsUtil.list_Mmap_get_some _ _ _ _ _ Hargv x Hin) as [bv Hbv];
            unfold Sep.has_key; rewrite Hbv; exact I ]).
    (* Step 6 (Hsat): the source rule, applied to a_src, gives a_src' sound on
       the source conclusions. *)
    assert (Hsrc_assum_s : all (clause_sound_for_model idx symbol idx_map m a_src) (seq_assumptions s))
      by (rewrite Hassum; exact Hsrc_assum).
    (* Step 6a: domain-confinement for a_src: every key of a_src is in forall_vars s. *)
    assert (Hconf_src : forall x, Sep.has_key x a_src -> In x (forall_vars s)).
    { intros x Hx.
      destruct (pullback_assignment_dom_converse a_opt sub2 x Hx) as (y & Hin_xy & Hhk_y).
      (* y has a key in a_opt; use Hconf to get y in the optimized forall_vars,
         then db_idxs_in_equiv to get has_key y (parent (equiv e_assum)). *)
      assert (Hy_assum : Sep.has_key y (parent (equiv e_assum))).
      { specialize (Hconf y Hhk_y).
        (* Reduce Hconf's forall_vars to the assumption atoms of the optimized sequent. *)
        unfold forall_vars in Hconf.
        cbn [seq_assumptions] in Hconf.
        (* After all the reductions, seq_assumptions is map atom_clause AA *)
        apply in_flat_map in Hconf.
        destruct Hconf as (cl & Hcl_in & Hy_cl).
        apply in_map_iff in Hcl_in.
        destruct Hcl_in as (a0 & Ha0_eq & Ha0_in).
        subst cl. cbn [clause_vars] in Hy_cl.
        pose proof (proj1 (in_db_to_atoms_iff_atom_in_db a0 (db e_assum)) Ha0_in) as Ha0_db.
        pose proof (db_idxs_in_equiv _ _ _ _ _ _ _ _ Hok_assum _ Ha0_db) as [Hka Hkr].
        destruct Hy_cl as [Hyret | Hyarg].
        - subst y. exact Hkr.
        - exact (in_all (fun i => Sep.has_key i (parent (equiv e_assum))) _ _ Hka Hyarg). }
      (* Now use domain confinement: x must have been in sub1, or else y would be fresh w.r.t e_assum. *)
      destruct (inb x (map fst sub1)) eqn:Hib.
      - (* x in keys sub1 -> forall_vars s *)
        assert (Hin_keys : In x (map fst sub1))
          by (apply (@inb_is_In idx Eqb_idx Eqb_idx_ok); rewrite Hib; exact I).
        apply in_map_iff in Hin_keys.
        destruct Hin_keys as ((x' & y') & Hxeq & Hin_pair).
        cbn [fst] in Hxeq. subst x'.
        pose proof (clauses_to_instance_sub_in_domain (map atom_clause atoms) []
                      (empty_egraph idx_zero unit) x y') as Hsd.
        rewrite Hcti_a in Hsd. specialize (Hsd Hin_pair).
        unfold forall_vars. rewrite Hassum.
        destruct Hsd as [Hnil | Hfv]; [ destruct Hnil | exact Hfv ].
      - (* x NOT in keys sub1 -> contradiction via clauses_to_instance_new_key_fresh *)
        exfalso.
        assert (Hnin : ~ In x (map fst sub1))
          by (intro Hc;
              apply (@inb_is_In idx Eqb_idx Eqb_idx_ok) in Hc;
              rewrite Hib in Hc; exact Hc).
        pose proof (clauses_to_instance_new_key_fresh Hlti Hlts Hltt (seq_conclusions s) sub1 e_assum x y
                      (Semantics.egraph_equiv_ok _ _ _ _ _ _ _ _ Hok_assum)) as Hfresh.
        rewrite Hcti_c in Hfresh.
        exact (Hfresh Hin_xy Hnin Hy_assum). }
    unfold model_satisfies_rule in Hsat.
    specialize (Hsat a_src Hkeys_src Hconf_src Hsrc_assum_s).
    destruct Hsat as [a_src' [Hext_src' Hconcl_src'] ].
    (* a_src is defined on every key of sub1 (sub1 keys are source vars). *)
    assert (Ha_src_sub1_def : forall x y, In (x,y) sub1 -> exists d, map.get a_src x = Some d)
      by (intros x y Hxy;
          pose proof (clauses_to_instance_sub_in_domain (map atom_clause atoms) []
                        (empty_egraph idx_zero unit) x y) as Hdom;
          rewrite Hcti_a in Hdom; specialize (Hdom Hxy);
          assert (Hin_fv : In x (forall_vars s))
            by (unfold forall_vars; rewrite Hassum;
                destruct Hdom as [Hnil | Hf]; [ destruct Hnil | exact Hf ]);
          pose proof (Hkeys_src x Hin_fv) as Hhk;
          unfold Sep.has_key in Hhk;
          destruct (map.get a_src x) as [d|] eqn:Hg; [ exists d; reflexivity | destruct Hhk ]).
    (* Step 7: push the conclusion clauses forward; i_c is sound on e_c2
       (= conclusion_inst). *)
    assert (Hren_in : forall x y, In (x,y) sub1 -> forall d, map.get a_src' x = Some d -> map.get i_e1 y = Some d).
    { intros x y Hxy d Hd.
      destruct (Ha_src_sub1_def x y Hxy) as [d0 Ha0].
      pose proof (Hext_src' _ _ Ha0) as Ha0'.
      assert (d = d0) as -> by congruence.
      apply (Hren_e1 x y Hxy d0 Ha0). }
    assert (Hsubdom_c : forall x y, In (x,y) sub1 -> Sep.has_key y (parent (equiv e_assum))).
    { intros x y Hxy.
      destruct (Ha_src_sub1_def x y Hxy) as [d0 Ha0].
      pose proof (Hren_e1 x y Hxy d0 Ha0) as Hi.
      apply (Semantics.interpretation_exact _ _ _ _ _ _ _ _ _ Hsnd_assum y).
      rewrite Hi; exact I. }
    pose proof (clauses_to_instance_preserves_ok Hlti Hlts Hltt m Hm (seq_conclusions s) sub1 e_assum i_e1 a_src'
       Hok_assum Hsnd_assum Hren_in Hsubdom_c Hconcl_src') as Hpo_c.
    rewrite Hcti_c in Hpo_c.
    destruct Hpo_c as [Hok_c0 [i_c [Hext_c [Hsnd_c0 [Hren_c Hdom_c] ] ] ] ].
    pose proof (@Semantics.rebuild_sound idx Eqb_idx Eqb_idx_ok lt idx_succ idx_zero symbol Eqb_symbol Eqb_symbol_ok symbol_map symbol_map_ok idx_map idx_map_ok idx_trie idx_trie_ok unit _ m Hm (fun _ => True) RFUEL) as Hrs_c.
    unfold vc in Hrs_c. specialize (Hrs_c e_c0). rewrite Hrb_c in Hrs_c. cbn [snd] in Hrs_c.
    specialize (Hrs_c Hok_c0). destruct Hrs_c as [Hok_c1 Hde_c].
    pose proof (proj1 (Hde_c i_c) Hsnd_c0) as Hsnd_c1.
    pose proof (force_equiv_preserves_sound m i_c e_c1 (Semantics.egraph_equiv_ok _ _ _ _ _ _ _ _ Hok_c1) Hsnd_c1) as Hsnd_fe.
    rewrite Hfe_c in Hsnd_fe. cbn [snd] in Hsnd_fe.
    (* Steps 8-9: the final witness [map.putmany i_c a_opt] extends a_opt and
       agrees with i_c on i_c's domain (adversary match); read back the
       optimized conclusions soundly under i_c. *)
    assert (Hext_final : map.extends (map.putmany i_c a_opt) a_opt)
      by (intros k v Hv;
          exact (@Properties.map.get_putmany_right idx (domain symbol m) (idx_map (domain symbol m))
                   (idx_map_ok (domain symbol m)) _ (@eqb_boolspec idx Eqb_idx Eqb_idx_ok)
                   i_c a_opt k v Hv)).
    assert (Hagree : map.extends (map.putmany i_c a_opt) i_c)
      by (intros k v Hk;
          destruct (map.get a_opt k) as [w|] eqn:Ha;
          [ assert (w = v) as Hwv;
            [ destruct (Hdom_c k v Hk) as [Hie1 | [x' Hx'] ];
              [ destruct (Hdom_e1 k v Hie1) as [Hempt | [x'' Hx''] ];
                [ rewrite map.get_empty in Hempt; discriminate
                | pose proof (get_pullback_assignment_some a_opt sub2 x'' k w (Hsub_mono x'' k Hx'') Ha) as Hsx;
                  pose proof (Hren_e1 x'' k ltac:(apply named_list_lookup_err_in; symmetry; exact Hx'') w Hsx) as Hie1';
                  congruence ]
              | pose proof (get_pullback_assignment_some a_opt sub2 x' k w Hx' Ha) as Hsx;
                pose proof (Hren_c x' k ltac:(apply named_list_lookup_err_in; symmetry; exact Hx') w (Hext_src' _ _ Hsx)) as Hic';
                congruence ]
            | subst w;
              exact (@Properties.map.get_putmany_right idx (domain symbol m) (idx_map (domain symbol m))
                       (idx_map_ok (domain symbol m)) _ (@eqb_boolspec idx Eqb_idx Eqb_idx_ok) i_c a_opt k v Ha) ]
          | rewrite (@Properties.map.get_putmany_left idx (domain symbol m) (idx_map (domain symbol m))
                       (idx_map_ok (domain symbol m)) _ (@eqb_boolspec idx Eqb_idx Eqb_idx_ok) i_c a_opt k Ha);
            exact Hk ]).
    exists (map.putmany i_c a_opt).
    split;
      [ exact Hext_final
      | apply (all_clause_sound_extend m i_c (map.putmany i_c a_opt) _ Hagree);
        apply all_app; split;
        [ apply SemanticsUtil.all_map_in; intros p Hp; apply incl_filter in Hp;
          destruct p as [px py];
          pose proof (in_all (clause_sound_for_model idx symbol idx_map m i_c) _ _
            (uf_eqs_sound m i_c e_c2 Hsnd_fe)
            (in_map (fun q => @eq_clause idx symbol (fst q) (snd q)) _ _ Hp)) as Hsp;
          cbn [uncurry fst snd] in Hsp |- *; exact Hsp
        | apply SemanticsUtil.all_map_in; intros a0 Ha0;
          exact (in_all (clause_sound_for_model idx symbol idx_map m i_c) _ _
            (db_to_atoms_sound m i_c e_c2 Hsnd_fe)
            (in_map (@atom_clause idx symbol) _ _
              (@QueryOpt.incl_remove_atoms idx Eqb_idx Eqb_idx_ok lt symbol Eqb_symbol Eqb_symbol_ok
                 symbol_map symbol_map_ok idx_map idx_trie idx_trie_ok unit AA e_c2 a0 Ha0))) ] ].
  Qed.

  (* ================================================================ *)
  (* OFF THE egraph_sound PATH -- DO NOT mistake these admits for      *)
  (* remaining work on egraph_sound.                                   *)
  (*                                                                   *)
  (* The three lemmas below ([optimize_sequent_forward],               *)
  (* [optimize_sequent_reverse], [optimize_sequent_equiv]) are the     *)
  (* GENERAL bidirectional equivalence -- a separate, still-incomplete *)
  (* deliverable.  egraph_sound consumes the PROVEN, 0-axiom sibling   *)
  (* [optimize_sequent_forward_atoms] (above), NOT these.              *)
  (*                                                                   *)
  (* Verified 2026-06-02 via [Print Assumptions egraph_sound]:         *)
  (* egraph_sound rests on EXACTLY ONE axiom                           *)
  (* ([egraph_reducing_equal'_to_pos], Admitted only because of its    *)
  (* single internal [schedule_sound] admit).  None of the three       *)
  (* lemmas below appear among its assumptions; they are consumed by   *)
  (* nothing outside this file's own [optimize_sequent_equiv].         *)
  (* The 6 admits here are therefore safe to ignore for egraph_sound.  *)
  (* ================================================================ *)
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
      intros a Hkeys Hconf Hass. exists a; split; [intros ? ? Hk; exact Hk | cbn; trivial].
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
