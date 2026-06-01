(* Source-rule soundness adapter (B0): the glue lemma
   model_satisfies_rule (lang_model l) (rule_to_log_rule ... name r)
   built on top of add_ctx_inversion (AddCtxInversion.v) and the
   (II) conclusion semantic core (ConclSemantic.v). *)
From Stdlib Require Import Lists.List Classes.RelationClasses BinNums.
Import ListNotations.
Open Scope list.

From coqutil Require Import Map.Interface Datatypes.Result.

From Utils Require Import Utils UnionFind Monad ExtraMaps VC Relations Result.
From Utils.EGraph Require Import Defs Semantics QueryOpt QueryOptSound.
Import Monad.StateMonad.
From Pyrosome.Theory Require Import Core ModelImpls.
Import Core.Notations.
From Pyrosome.Tools.EGraph Require Import Defs.
From Pyrosome.Tools.EGraph Require Import Theorems AddCtxInversion ConclSemantic.

Section WithVar.
  Context (V : Type)
    {V_Eqb : Eqb V}
    {V_Eqb_ok : Eqb_ok V_Eqb}
    {V_default : WithDefault V}.

  Notation named_list := (@named_list V).
  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).

  Notation wf_subst l := (wf_subst (Model:= core_model l)).
  Notation wf_ctx l := (wf_ctx (Model:= core_model l)).

  Context
    (V_map : forall A, map.map V A)
      (V_map_plus : ExtraMaps.map_plus V_map)
      (V_map_ok : forall A, map.ok (V_map A))
      (V_trie : forall A, map.map (list V) A)
      (V_trie_ok : forall A, map.ok (V_trie A)).

  Notation instance := (instance V V V_map V_map V_trie).
  Notation atom := (atom V V).

  Context (succ : V -> V).
  Context (sort_of : V).
  Context (lt : V -> V -> Prop).
  Context (lt_asymmetric : Asymmetric lt)
    (lt_succ : forall x, lt x (succ x))
    (lt_trans : Transitive lt).

  Local Notation lang_model := (@Theorems.lang_model V V_Eqb sort_of).

  (* ===== assumption bridge: from [a] sound on the read-back assumption
     atoms, recover soundness on every atom_in_egraph. ===== *)
  Lemma assumption_atoms_sound (m : model V) (a : V_map (domain V m))
      (e : instance unit)
      (Hall : all (clause_sound_for_model V V V_map m a)
                  (map atom_clause (db_to_atoms (db e))))
    : forall al, @atom_in_egraph V V V_map V_map V_trie unit al e ->
                 atom_sound_for_model V V V_map m a al.
  Proof.
    intros al Hin.
    assert (Hin' : In al (db_to_atoms (db e))).
    { apply (proj2 (in_db_to_atoms_iff_atom_in_db V V_Eqb V_Eqb_ok lt succ V_default
                      V V_Eqb V_Eqb_ok V_map V_map_ok V_trie V_trie_ok al (db e))).
      exact Hin. }
    pose proof (in_map atom_clause _ _ Hin') as Hin_map.
    pose proof (in_all _ _ _ Hall Hin_map) as Hsnd.
    exact Hsnd.
  Qed.

  Section Adapter.
    Context (l : lang) (Hwf : wf_lang l) (Hsof : fresh sort_of l) (rf : nat).

    Local Notation X := unit.
    Local Notation HX := (@unit_analysis V V).

    (* ===== (II) conclusion obligation for term rules — Admitted placeholder ===== *)
    Lemma term_rule_concl_obligation name c args t
        (a : V_map (domain V (lang_model l)))
        (sg : subst)
        (Hsg : wf_subst l [] sg c)
        (Hmapfst : map fst sg = map fst c)
        (Hfaith : forall x, In x (map fst (fst (add_ctx succ sort_of l false false c
                                                  (empty_egraph V_default X)))) ->
                    map.get a (named_list_lookup default
                                (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))) x)
                      = Some (inl (named_list_lookup default sg x)))
        (Hin : In (name, term_rule c args t) l)
      : exists a' : V_map (domain V (lang_model l)),
          map.extends a' a /\
          all (clause_sound_for_model V V V_map (lang_model l) a')
            (seq_conclusions (@rule_to_log_rule V V_Eqb V_default V_map V_trie succ sort_of l
                                X HX rf name (term_rule c args t))).
    Admitted.

    (* ===== (B0) term-rule adapter ===== *)
    Lemma model_satisfies_rule_adapter_term name c args t
        (Hin : In (name, term_rule c args t) l)
        (Hsucc : fst (rebuild rf (snd (add_ctx succ sort_of l false false c
                                         (empty_egraph V_default X)))) = Success tt)
      : @model_satisfies_rule V V V_map (lang_model l)
          (@rule_to_log_rule V V_Eqb V_default V_map V_trie succ sort_of l
             X HX rf name (term_rule c args t)).
    Proof.
      unfold model_satisfies_rule.
      intros a Hkeys Hassum.
      unfold rule_to_log_rule in Hassum |- *.
      unfold sequent_of_states in Hassum.
      cbn [seq_assumptions] in Hassum.
      unfold Monad.Mbind, Monad.Mret, StateMonad.state_monad in Hassum.
      (* Reduce the [assumptions ;; rebuild] state computation to clean form. *)
      assert (Heq_e :
        snd (let (x, y) := add_ctx succ sort_of l false false c (empty_egraph V_default X) in
             let (_, y0) := rebuild rf y in (x, y0))
        = snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))).
      { destruct (add_ctx succ sort_of l false false c (empty_egraph V_default X)) as [sub e1].
        cbn [snd]. destruct (rebuild rf e1) as [r2 e2]. reflexivity. }
      rewrite Heq_e in Hassum.
      clear Heq_e Hkeys.
      assert (Hwfc : wf_ctx l c).
      { pose proof (rule_in_wf _ _ Hwf Hin) as Hr. rewrite app_nil_r in Hr.
        rewrite invert_wf_term_rule in Hr. destruct Hr as [Hc _]. exact Hc. }
      (* (I) assumption inversion: recover a wf substitution [sg] of [c]. *)
      pose proof (assumption_atoms_sound (lang_model l) a _ Hassum) as Hsnd_atoms.
      pose proof (@add_ctx_inversion V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok
                    succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof rf a c Hwfc
                    (@add_ctx_good_worklist V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok
                       succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc)
                    Hsucc Hsnd_atoms) as Hinv.
      destruct Hinv as [sg [ Hsg [ Hmapfst Hfaith ] ] ].
      (* (II) conclusion construction. *)
      exact (term_rule_concl_obligation name c args t a sg Hsg Hmapfst Hfaith Hin).
    Qed.

    (* ===== (II) conclusion obligation for sort rules — Admitted placeholder ===== *)
    Lemma sort_rule_concl_obligation name c args
        (a : V_map (domain V (lang_model l)))
        (sg : subst)
        (Hsg : wf_subst l [] sg c)
        (Hmapfst : map fst sg = map fst c)
        (Hfaith : forall x, In x (map fst (fst (add_ctx succ sort_of l false false c
                                                  (empty_egraph V_default X)))) ->
                    map.get a (named_list_lookup default
                                (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))) x)
                      = Some (inl (named_list_lookup default sg x)))
        (Hin : In (name, sort_rule c args) l)
      : exists a' : V_map (domain V (lang_model l)),
          map.extends a' a /\
          all (clause_sound_for_model V V V_map (lang_model l) a')
            (seq_conclusions (@rule_to_log_rule V V_Eqb V_default V_map V_trie succ sort_of l
                                X HX rf name (sort_rule c args))).
    Admitted.

    (* ===== (B0) sort-rule adapter ===== *)
    Lemma model_satisfies_rule_adapter_sort name c args
        (Hin : In (name, sort_rule c args) l)
        (Hsucc : fst (rebuild rf (snd (add_ctx succ sort_of l false false c
                                         (empty_egraph V_default X)))) = Success tt)
      : @model_satisfies_rule V V V_map (lang_model l)
          (@rule_to_log_rule V V_Eqb V_default V_map V_trie succ sort_of l
             X HX rf name (sort_rule c args)).
    Proof.
      unfold model_satisfies_rule.
      intros a Hkeys Hassum.
      unfold rule_to_log_rule in Hassum |- *.
      unfold sequent_of_states in Hassum.
      cbn [seq_assumptions] in Hassum.
      unfold Monad.Mbind, Monad.Mret, StateMonad.state_monad in Hassum.
      assert (Heq_e :
        snd (let (x, y) := add_ctx succ sort_of l false false c (empty_egraph V_default X) in
             let (_, y0) := rebuild rf y in (x, y0))
        = snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))).
      { destruct (add_ctx succ sort_of l false false c (empty_egraph V_default X)) as [sub e1].
        cbn [snd]. destruct (rebuild rf e1) as [r2 e2]. reflexivity. }
      rewrite Heq_e in Hassum.
      clear Heq_e Hkeys.
      assert (Hwfc : wf_ctx l c).
      { pose proof (rule_in_wf _ _ Hwf Hin) as Hr. rewrite app_nil_r in Hr.
        rewrite invert_wf_sort_rule in Hr. destruct Hr as [Hc _]. exact Hc. }
      pose proof (assumption_atoms_sound (lang_model l) a _ Hassum) as Hsnd_atoms.
      pose proof (@add_ctx_inversion V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok
                    succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof rf a c Hwfc
                    (@add_ctx_good_worklist V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok
                       succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc)
                    Hsucc Hsnd_atoms) as Hinv.
      destruct Hinv as [sg [ Hsg [ Hmapfst Hfaith ] ] ].
      exact (sort_rule_concl_obligation name c args a sg Hsg Hmapfst Hfaith Hin).
    Qed.

  End Adapter.
End WithVar.
