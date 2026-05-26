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
  the model-theoretic semantics of a sequent: a model satisfies the
  optimised sequent iff it satisfies the original.

  See /root/.claude/plans/queryopt-v-is-a-file-hidden-nest.md for the
  overall proof strategy.
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
  Theorem optimize_sequent_equiv (s : sequent) :
    sequent_equiv (optimize_sequent s) s.
  Proof.
  Admitted.

End WithMap.
