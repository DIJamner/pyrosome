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
    induction cs as [|c cs IH]; intros sub0 e0 i Hok Hsnd Hren Hcs.
    - cbn. split; [exact Hok|]. exists i.
      split; [intros ? ? Hk; exact Hk | exact Hsnd].
    - cbn. unfold add_clause_to_instance.
      destruct c as [x y | a].
      + (* eq_clause: use alloc_sound twice + union_sound + IH. *)
        admit.
      + (* atom_clause: use alloc_sound (for rename_atom's chain) +
           update_entry_sound + IH.  Witness for each fresh id comes
           from a_src via the extended renaming. *)
        admit.
  Admitted.

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
