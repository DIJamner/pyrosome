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

  (* Helper: transfer list_Mmap soundness under the setoid compatibility
     condition (Hcompat). *)
  Lemma list_Mmap_get_setoid (m : model V) (i a' : V_map (domain V m))
      (Hcompat : forall k d, map.get i k = Some d ->
                   exists d', map.get a' k = Some d' /\ domain_eq V m d d')
      (args : list V) (iargs : list (domain V m))
      (Hmm : list_Mmap (map.get i) args = Some iargs)
    : exists a'args, list_Mmap (map.get a') args = Some a'args
                     /\ all2 (domain_eq V m) iargs a'args.
  Proof.
    revert iargs Hmm.
    induction args as [| x xs IH]; intros iargs Hmm.
    - cbn in Hmm. injection Hmm as <-. exists []. split; reflexivity.
    - cbn in Hmm.
      destruct (map.get i x) as [dx|] eqn:Hx.
      2: { discriminate. }
      destruct (list_Mmap (map.get i) xs) as [dxs|] eqn:Hxs.
      2: { discriminate. }
      injection Hmm as <-.
      destruct (IH dxs eq_refl) as (a'xs & Ha'xs & Hall2).
      destruct (Hcompat x dx Hx) as (dx' & Hx' & Heq).
      exists (dx' :: a'xs).
      split.
      + cbn. rewrite Hx'. rewrite Ha'xs. reflexivity.
      + cbn. split; assumption.
  Qed.

  (* Setoid transfer: if [i] and [a'] agree up to [domain_eq m] on every
     key (Hcompat), then soundness of a clause list under [i] implies
     soundness under [a']. *)
  Lemma all_clause_sound_setoid (m : model V) (Hm : model_ok V m)
      (i a' : V_map (domain V m)) (cs : list (clause V V))
      (Hcompat : forall k d, map.get i k = Some d ->
                   exists d', map.get a' k = Some d' /\ domain_eq V m d d')
    : all (clause_sound_for_model V V V_map m i) cs ->
      all (clause_sound_for_model V V V_map m a') cs.
  Proof.
    induction cs as [| c cs IH]; intro Hall.
    - exact I.
    - destruct Hall as [Hc Hcs].
      split.
      2: { exact (IH Hcs). }
      destruct c as [x y | a].
      + (* eq_clause x y *)
        unfold clause_sound_for_model, eq_sound_for_model in *.
        destruct (map.get i x) as [dx|] eqn:Hx.
        2: { cbn [Is_Some_satisfying] in Hc. contradiction. }
        cbn [Is_Some_satisfying] in Hc.
        destruct (map.get i y) as [dy|] eqn:Hy.
        2: { cbn [Is_Some_satisfying] in Hc. contradiction. }
        cbn [Is_Some_satisfying] in Hc.
        destruct (Hcompat x dx Hx) as (dx' & Hx' & Heq_x).
        destruct (Hcompat y dy Hy) as (dy' & Hy' & Heq_y).
        rewrite Hx', Hy'.
        cbn [Is_Some_satisfying].
        pose proof (domain_eq_PER V (model_ok:=Hm)) as Hper.
        pose proof (@PER_Symmetric _ _ Hper) as Hsym.
        pose proof (@PER_Transitive _ _ Hper) as Htrans.
        exact (Htrans _ _ _ (Htrans _ _ _ (Hsym _ _ Heq_x) Hc) Heq_y).
      + (* atom_clause a *)
        unfold clause_sound_for_model, atom_sound_for_model in *.
        destruct (list_Mmap (map.get i) (atom_args a)) as [iargs|] eqn:Hmm.
        2: { cbn [Is_Some_satisfying] in Hc. contradiction. }
        cbn [Is_Some_satisfying] in Hc.
        destruct (map.get i (atom_ret a)) as [iret|] eqn:Hret.
        2: { cbn [Is_Some_satisfying] in Hc. contradiction. }
        cbn [Is_Some_satisfying] in Hc.
        destruct (list_Mmap_get_setoid m i a' Hcompat (atom_args a) iargs Hmm)
          as (a'args & Ha'args & Hall2).
        destruct (Hcompat (atom_ret a) iret Hret) as (a'ret & Hret' & Heq_ret).
        rewrite Ha'args, Hret'.
        cbn [Is_Some_satisfying].
        exact (@interprets_to_preserved V m Hm _ iargs a'args iret a'ret Hc Hall2 Heq_ret).
  Qed.

  Section Adapter.
    Context (l : lang) (Hwf : wf_lang l) (Hsof : fresh sort_of l) (rf : nat).

    Local Notation X := unit.
    Local Notation HX := (@unit_analysis V V).

    Local Notation egraph_ok :=
      (Semantics.egraph_ok V lt V V_map V_map V_trie X).
    Local Notation egraph_sound_for_interpretation :=
      (Semantics.egraph_sound_for_interpretation V V V_map V_map V_trie X).
    Local Notation args_in_instance :=
      (@Theorems.args_in_instance V V_Eqb V_map sort_of).
    Local Notation instance := (Defs.instance V V V_map V_map V_trie X).

    (* ===== assumption egraph is ok and sound ===== *)
    Lemma assumption_egraph_sound c (Hwfc : wf_ctx l c) (sg : subst)
        (Hsg : wf_subst l [] sg c)
      : egraph_ok (snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))
        /\ exists i1,
             egraph_sound_for_interpretation (lang_model l) i1
               (snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))
             /\ map fst (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))) = map fst c
             /\ args_in_instance l (map snd sg) i1
                  (map snd (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))).
    Proof.
      cbn zeta.
      (* Step 1: empty egraph is ok and sound *)
      destruct (Semantics.empty_sound_for_interpretation
                  V lt succ V_default V V_map (V_map_ok) V_map (V_map_ok)
                  V_trie X (lang_model l))
        as [Hok_empty Hsnd_empty].
      (* Step 2: add_ctx_sound gives ctx_post *)
      pose proof (@Theorems.add_ctx_sound
                    V V_Eqb V_Eqb_ok V_default V_map (V_map_ok) V_trie V_trie_ok
                    succ sort_of lt lt_asymmetric lt_succ lt_trans
                    X HX l Hwf Hsof false
                    sg c Hsg Hwfc
                    map.empty)
        as Hvc_ctx.
      unfold vc in Hvc_ctx.
      specialize (Hvc_ctx (empty_egraph V_default X)).
      unfold Theorems.ctx_post in Hvc_ctx.
      specialize (Hvc_ctx Hok_empty Hsnd_empty).
      destruct Hvc_ctx as [i1 (Hext1 & Hfst1 & Hai1)].
      (* Unpack extending_sound *)
      destruct Hext1 as (Hok_ctx & _ & Hsnd_ctx & _).
      (* Step 3: rebuild_sound *)
      pose proof (@Semantics.rebuild_sound
                    V V_Eqb V_Eqb_ok lt succ V_default V V_Eqb V_Eqb_ok
                    V_map V_map_ok V_map V_map_ok
                    V_trie V_trie_ok unit HX
                    (lang_model l)
                    (@Theorems.lang_model_ok V V_Eqb V_Eqb_ok sort_of l Hsof Hwf)
                    (fun _ => True) rf)
        as Hvc_rb.
      unfold vc in Hvc_rb.
      specialize (Hvc_rb (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))).
      cbn [snd] in Hvc_rb.
      specialize (Hvc_rb Hok_ctx).
      destruct Hvc_rb as [Hok_assum Hde_assum].
      split; [exact Hok_assum|].
      (* Step 4: transfer soundness of i1 across rebuild *)
      pose proof (proj1 (Hde_assum i1) Hsnd_ctx) as Hsnd_assum.
      exists i1. split; [exact Hsnd_assum|].
      split; [exact Hfst1|exact Hai1].
    Qed.

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
