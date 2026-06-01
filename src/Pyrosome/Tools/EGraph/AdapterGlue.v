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
  Notation wf_args l := (wf_args (Model:= core_model l)).
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
    Local Notation atom_tree :=
      (@Theorems.atom_tree V V_Eqb V_default V_map V_trie X).
    Local Notation atom_tree_sort :=
      (@Theorems.atom_tree_sort V V_Eqb V_default V_map V_trie X).

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

    (* ===== conclusion forward chain: given wf_subst, produce a sound interpretation
         for the conclusion egraph (after add_open_term + rebuild + force_equiv). ===== *)
    Lemma conclusion_egraph_sound name c args t (sg : subst)
        (Hin : In (name, term_rule c args t) l)
        (Hsg : wf_subst l [] sg c)
      : let sub    := fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)) in
        let e_assum := snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))) in
        let e_open  := snd (add_open_term succ sort_of l true false sub (con name (id_args c)) e_assum) in
        let e_concl := snd (force_equiv V V_Eqb V V_map V_map V_trie (X:=X)
                              (snd (rebuild rf e_open))) in
        exists i2,
          egraph_sound_for_interpretation (lang_model l) i2 e_concl
          /\ args_in_instance l (map snd sg) i2 (map snd sub).
    Proof.
      (* Unfold the let-bindings *)
      cbn zeta.
      set (sub    := fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))).
      set (e_ctx  := snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))).
      set (e_assum := snd (rebuild rf e_ctx)).
      (* Step 1: derive wf_ctx l c from rule membership *)
      assert (Hwfc : wf_ctx l c).
      { pose proof (rule_in_wf _ _ Hwf Hin) as Hr. rewrite app_nil_r in Hr.
        rewrite invert_wf_term_rule in Hr. destruct Hr as [Hc _]. exact Hc. }
      (* Step 2: use assumption_egraph_sound *)
      pose proof (assumption_egraph_sound c Hwfc sg Hsg)
        as (Hok_assum & i1 & Hsnd_assum & Hfst_sub & Hai1).
      (* Step 3: derive wf_term l c (con name (id_args c)) t *)
      assert (Hwft : wf_term l c (con name (id_args c)) t).
      { replace t with (t[/id_subst c/]); [| basic_core_crush].
        eapply wf_term_by; eauto.
        eapply id_args_wf; eauto with utils. }
      (* Step 4+5: apply add_open_term_sound *)
      pose proof (@Theorems.add_open_term_sound
                    V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok
                    succ sort_of lt lt_asymmetric lt_succ lt_trans
                    X HX l Hwf Hsof true
                    c sub (map snd sg) (con name (id_args c)) t
                    (@Theorems.wf_args_from_wf_subst V V_Eqb l [] sg c Hsg)
                    Hwft Hwfc
                    (eq_sym Hfst_sub) i1)
        as Hvc_open.
      unfold vc in Hvc_open.
      specialize (Hvc_open e_assum).
      unfold Theorems.open_term_post in Hvc_open.
      specialize (Hvc_open Hok_assum Hsnd_assum Hai1).
      destruct Hvc_open as [i2 (Hext_open & _)].
      destruct Hext_open as (Hok_open & Hext12 & Hsnd_open & _).
      set (e_open := snd (add_open_term succ sort_of l true false sub
                            (con name (id_args c)) e_assum)).
      (* Step 6: rebuild_sound on e_open *)
      pose proof (@Semantics.rebuild_sound
                    V V_Eqb V_Eqb_ok lt succ V_default V V_Eqb V_Eqb_ok
                    V_map V_map_ok V_map V_map_ok
                    V_trie V_trie_ok unit HX
                    (lang_model l)
                    (@Theorems.lang_model_ok V V_Eqb V_Eqb_ok sort_of l Hsof Hwf)
                    (fun _ => True) rf)
        as Hvc_rb2.
      unfold vc in Hvc_rb2.
      specialize (Hvc_rb2 e_open).
      cbn [snd] in Hvc_rb2.
      specialize (Hvc_rb2 Hok_open).
      destruct Hvc_rb2 as [Hok_rb2 Hde_rb2].
      pose proof (proj1 (Hde_rb2 i2) Hsnd_open) as Hsnd_rb2.
      set (e_rb2 := snd (rebuild rf e_open)).
      (* Step 7: force_equiv_preserves_sound *)
      pose proof (@QueryOptSound.force_equiv_preserves_sound
                    V V_Eqb V_Eqb_ok lt V V_map V_map V_map_ok V_trie
                    (lang_model l) i2 e_rb2
                    (Semantics.egraph_equiv_ok V lt V V_map V_map V_trie unit e_rb2 Hok_rb2)
                    Hsnd_rb2)
        as Hsnd_concl.
      (* Step 8: args_in_instance monotone under i1 → i2 *)
      pose proof (@Theorems.args_in_instance_monotone
                    V V_Eqb V_map sort_of l (map snd sg) i1 i2
                    (map snd sub) Hext12 Hai1)
        as Hai2.
      exists i2.
      split.
      - exact Hsnd_concl.
      - exact Hai2.
    Qed.

    (* ===== R2: lift i2 soundness on e_concl to all seq_conclusions clauses ===== *)
    Lemma concl_clauses_sound_term name c args t (sg : subst)
        (Hin : In (name, term_rule c args t) l)
        (Hsg : wf_subst l [] sg c)
        (i2 : V_map (domain V (lang_model l)))
        (Hsnd : egraph_sound_for_interpretation (lang_model l) i2
                  (snd (force_equiv V V_Eqb V V_map V_map V_trie (X:=X)
                          (snd (rebuild rf
                            (snd (add_open_term succ sort_of l true false
                                    (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                                    (con name (id_args c))
                                    (snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))))))))))
      : all (clause_sound_for_model V V V_map (lang_model l) i2)
            (seq_conclusions (@rule_to_log_rule V V_Eqb V_default V_map V_trie succ sort_of l X HX rf name (term_rule c args t))).
    Proof.
      unfold rule_to_log_rule, sequent_of_states.
      cbn [seq_conclusions].
      unfold Monad.Mbind, Monad.Mret, StateMonad.state_monad.
      cbn beta iota.
      set (sub    := fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))).
      set (e_ctx  := snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))).
      set (e_assum := snd (rebuild rf e_ctx)).
      set (e_open  := snd (add_open_term succ sort_of l true false sub (con name (id_args c)) e_assum)).
      set (e_rb2   := snd (rebuild rf e_open)).
      set (e_concl := snd (force_equiv V V_Eqb V V_map V_map V_trie (X:=X) e_rb2)).
      (* Fold the Hsnd hypothesis: its raw expression equals e_concl by definitional equality *)
      change (egraph_sound_for_interpretation (lang_model l) i2 e_concl) in Hsnd.
      (* Fold conclusion_inst to e_concl via the destruct trick *)
      assert (Heq_concl :
        snd (uncurry
          (fun (a : list (V * V)) (x : instance) =>
           let (x0, y) := add_open_term succ sort_of l true false a (con name (id_args c)) x in
           let (_, y0) := rebuild rf y in
           let (_, y1) := force_equiv V V_Eqb V V_map V_map V_trie y0 in
           (x0, y1))
          (let (x, y) := add_ctx succ sort_of l false false c (empty_egraph V_default X) in
           let (_, y0) := rebuild rf y in (x, y0))) = e_concl).
      { unfold e_concl, e_rb2, e_open, e_assum, e_ctx, sub.
        unfold uncurry.
        destruct (add_ctx succ sort_of l false false c (empty_egraph V_default X)) as [sub0 e1].
        cbn [fst snd].
        destruct (rebuild rf e1) as [r2 e2]. cbn [fst snd].
        destruct (add_open_term succ sort_of l true false sub0 (con name (id_args c)) e2) as [sub3 e3].
        cbn [fst snd].
        destruct (rebuild rf e3) as [r4 e4]. cbn [fst snd].
        destruct (force_equiv V V_Eqb V V_map V_map V_trie e4) as [r5 e5]. cbn [fst snd].
        reflexivity. }
      (* Fold assumption egraph to e_assum *)
      assert (Heq_assum :
        snd (let (x, y) := add_ctx succ sort_of l false false c (empty_egraph V_default X) in
             let (_, y0) := rebuild rf y in (x, y0)) = e_assum).
      { unfold e_assum, e_ctx.
        destruct (add_ctx succ sort_of l false false c (empty_egraph V_default X)) as [sub0 e1].
        cbn [snd fst].
        destruct (rebuild rf e1) as [r2 e2]. reflexivity. }
      rewrite Heq_concl, Heq_assum.
      apply all_app; split.
      - (* eq_clause half via uf_eqs_sound *)
        apply SemanticsUtil.all_map_in.
        intros p Hp.
        apply incl_filter in Hp.
        destruct p as [px py].
        pose proof (in_all _ _ _
          (@QueryOptSound.uf_eqs_sound V V_Eqb V_Eqb_ok V V_map V_map V_map_ok V_trie
             (lang_model l) i2 e_concl Hsnd)
          (in_map (fun q => @eq_clause V V (fst q) (snd q)) _ _ Hp)) as Hsp.
        cbn [uncurry fst snd] in Hsp |- *.
        exact Hsp.
      - (* atom_clause half via db_to_atoms_sound + incl_remove_atoms *)
        apply SemanticsUtil.all_map_in.
        intros a0 Ha0.
        (* incl_remove_atoms: X is implicit, must be provided separately *)
        pose proof (@QueryOpt.incl_remove_atoms V V_Eqb V_Eqb_ok lt V V_Eqb V_Eqb_ok
           V_map V_map_ok V_map V_trie V_trie_ok) as Hira.
        pose proof (Hira X (db_to_atoms (db e_assum)) e_concl a0 Ha0) as Hin_concl.
        exact (in_all _ _ _
          (@QueryOptSound.db_to_atoms_sound V V_Eqb V_Eqb_ok lt succ V_default V V_Eqb V_Eqb_ok
             V_map V_map_ok V_map V_trie V_trie_ok (lang_model l) i2 e_concl Hsnd)
          (in_map (@atom_clause V V) _ _ Hin_concl)).
    Qed.

    (* ===== R3: relational readback-agreement (the one non-mechanical lemma) =====
       Two interps j1,j2 both sound on the assumption egraph eF's atoms, agreeing
       up to domain_eq on the readback leaves, agree up to domain_eq on every id
       carrying an atom_tree.  Purely relational (no term denotation): the con case
       is closed by interprets_to_functional.  Mirrors atom_tree_to_represents. *)
    Lemma atom_tree_args_deq
        (j1 j2 : V_map (domain V (lang_model l)))
        (eF : instance) (sub : named_list V) (cc c' : ctx)
        (Hsnd1 : forall al, atom_in_egraph al eF ->
                   atom_sound_for_model V V V_map (lang_model l) j1 al)
        (Hsnd2 : forall al, atom_in_egraph al eF ->
                   atom_sound_for_model V V V_map (lang_model l) j2 al)
        (Hleaf : forall x, In x (map fst sub) ->
                   exists d1 d2,
                     map.get j1 (named_list_lookup default sub x) = Some d1
                     /\ map.get j2 (named_list_lookup default sub x) = Some d2
                     /\ domain_eq V (lang_model l) d1 d2)
        (Hdom : map fst cc = map fst sub)
        (s : list term)
        (Hwfa : wf_args l cc s c')
        (IHs : all (fun e => forall t, wf_term l cc e t -> forall xe,
                   atom_tree eF sub e xe ->
                   exists d1 d2, map.get j1 xe = Some d1
                              /\ map.get j2 xe = Some d2
                              /\ domain_eq V (lang_model l) d1 d2) s)
      : forall sids, Forall2 (atom_tree eF sub) s sids ->
          exists d1s d2s,
            list_Mmap (map.get j1) sids = Some d1s
            /\ list_Mmap (map.get j2) sids = Some d2s
            /\ all2 (domain_eq V (lang_model l)) d1s d2s.
    Proof.
      revert IHs; induction Hwfa; intros IHs sids Htrees.
      - safe_invert Htrees. exists [], []. cbn. tauto.
      - safe_invert Htrees.
        destruct IHs as [IHe IHs0].
        match goal with
          Ht0 : atom_tree eF sub _ ?y0, Htl : Forall2 (atom_tree eF sub) _ ?yl |- _ =>
            destruct (IHe _ ltac:(eassumption) y0 Ht0) as (d1 & d2 & Hg1 & Hg2 & Hd);
            destruct (IHHwfa IHs0 yl Htl) as (d1s & d2s & Hm1 & Hm2 & Hds)
        end.
        exists (d1 :: d1s), (d2 :: d2s).
        cbn [list_Mmap].
        rewrite Hg1, Hg2, Hm1, Hm2. cbn [Mbind Mret].
        split; [reflexivity|]. split; [reflexivity|].
        cbn [all2]. split; assumption.
    Qed.

    Lemma atom_tree_deq
        (j1 j2 : V_map (domain V (lang_model l)))
        (eF : instance) (sub : named_list V) (cc : ctx)
        (Hsnd1 : forall al, atom_in_egraph al eF ->
                   atom_sound_for_model V V V_map (lang_model l) j1 al)
        (Hsnd2 : forall al, atom_in_egraph al eF ->
                   atom_sound_for_model V V V_map (lang_model l) j2 al)
        (Hleaf : forall x, In x (map fst sub) ->
                   exists d1 d2,
                     map.get j1 (named_list_lookup default sub x) = Some d1
                     /\ map.get j2 (named_list_lookup default sub x) = Some d2
                     /\ domain_eq V (lang_model l) d1 d2)
        (Hdom : map fst cc = map fst sub)
      : forall e t, wf_term l cc e t -> forall xe,
          atom_tree eF sub e xe ->
          exists d1 d2, map.get j1 xe = Some d1
                     /\ map.get j2 xe = Some d2
                     /\ domain_eq V (lang_model l) d1 d2.
    Proof.
      intro e; induction e as [x | n s IHs] using term_ind; intros t Hwt xe Htree.
      - safe_invert Htree.
        assert (In x (map fst cc)) as Hxc.
        { change (In x (map fst cc)) with (ws_term (map fst cc) (var x)).
          eapply wf_term_implies_ws; eauto with lang_core. }
        rewrite Hdom in Hxc.
        apply Hleaf; exact Hxc.
      - safe_invert Htree.
        apply WfCutElim.invert_wf_term_con in Hwt.
        destruct Hwt as (c'0 & args0 & t' & Hin & Hwfa & _).
        assert (IHsall : all (fun e => forall t, wf_term l cc e t -> forall xe,
                   atom_tree eF sub e xe ->
                   exists d1 d2, map.get j1 xe = Some d1
                              /\ map.get j2 xe = Some d2
                              /\ domain_eq V (lang_model l) d1 d2) s).
        { clear -IHs. induction s as [|e0 s0 IH]; cbn; [exact I|].
          destruct IHs as [IHe0 IHs0]. split; [exact IHe0 | exact (IH IHs0)]. }
        match goal with
          Htrees : Forall2 (atom_tree eF sub) s ?sids,
          Hatom : atom_in_egraph (Build_atom n ?sids xe) eF |- _ =>
            destruct (atom_tree_args_deq j1 j2 eF sub cc c'0 Hsnd1 Hsnd2 Hleaf Hdom
                        s Hwfa IHsall sids Htrees) as (d1s & d2s & Hm1 & Hm2 & Hds);
            pose proof (Hsnd1 _ Hatom) as Hsa1;
            pose proof (Hsnd2 _ Hatom) as Hsa2
        end.
        unfold atom_sound_for_model in Hsa1, Hsa2.
        cbn [atom_args atom_ret atom_fn] in Hsa1, Hsa2.
        rewrite Hm1 in Hsa1. cbn [Is_Some_satisfying] in Hsa1.
        rewrite Hm2 in Hsa2. cbn [Is_Some_satisfying] in Hsa2.
        destruct (map.get j1 xe) as [out1|] eqn:Ho1;
          [| cbn [Is_Some_satisfying] in Hsa1; contradiction].
        destruct (map.get j2 xe) as [out2|] eqn:Ho2;
          [| cbn [Is_Some_satisfying] in Hsa2; contradiction].
        cbn [Is_Some_satisfying] in Hsa1, Hsa2.
        exists out1, out2. split; [reflexivity|]. split; [reflexivity|].
        pose proof (@Theorems.lang_model_ok V V_Eqb V_Eqb_ok sort_of l Hsof Hwf) as Hmok.
        exact (@interprets_to_functional V (lang_model l) Hmok n d1s d2s out1 out2 Hsa1 Hsa2 Hds).
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
