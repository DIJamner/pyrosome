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
     condition (Hcompat), guarded by membership in args. *)
  Lemma list_Mmap_get_setoid (m : model V) (i a' : V_map (domain V m))
      (args : list V)
      (Hcompat : forall k, In k args -> forall d, map.get i k = Some d ->
                   exists d', map.get a' k = Some d' /\ domain_eq V m d d')
      (iargs : list (domain V m))
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
      destruct (IH (fun k Hk => Hcompat k (in_cons _ k _ Hk)) dxs eq_refl)
        as (a'xs & Ha'xs & Hall2).
      destruct (Hcompat x (in_eq x xs) dx Hx) as (dx' & Hx' & Heq).
      exists (dx' :: a'xs).
      split.
      + cbn. rewrite Hx'. rewrite Ha'xs. reflexivity.
      + cbn. split; assumption.
  Qed.

  (* Setoid transfer: if [i] and [a'] agree up to [domain_eq m] on the keys
     that appear in (clause_vars c) for each [c] in [cs] (Hcompat), then
     soundness of [cs] under [i] implies soundness under [a']. *)
  Lemma all_clause_sound_setoid (m : model V) (Hm : model_ok V m)
      (i a' : V_map (domain V m)) (cs : list (clause V V))
      (Hcompat : forall c, In c cs -> forall k, In k (clause_vars V V c) ->
                   forall d, map.get i k = Some d ->
                     exists d', map.get a' k = Some d' /\ domain_eq V m d d')
    : all (clause_sound_for_model V V V_map m i) cs ->
      all (clause_sound_for_model V V V_map m a') cs.
  Proof.
    induction cs as [| c cs IH]; intro Hall.
    - exact I.
    - destruct Hall as [Hc Hcs].
      split.
      2: { exact (IH (fun c0 Hc0 => Hcompat c0 (in_cons _ c0 _ Hc0)) Hcs). }
      destruct c as [x y | a].
      + (* eq_clause x y; clause_vars V V (eq_clause x y) = [x; y] *)
        unfold clause_sound_for_model, eq_sound_for_model in *.
        destruct (map.get i x) as [dx|] eqn:Hx.
        2: { cbn [Is_Some_satisfying] in Hc. contradiction. }
        cbn [Is_Some_satisfying] in Hc.
        destruct (map.get i y) as [dy|] eqn:Hy.
        2: { cbn [Is_Some_satisfying] in Hc. contradiction. }
        cbn [Is_Some_satisfying] in Hc.
        destruct (Hcompat (eq_clause x y) (in_eq _ _) x
                    (or_introl eq_refl) dx Hx)
          as (dx' & Hx' & Heq_x).
        destruct (Hcompat (eq_clause x y) (in_eq _ _) y
                    (or_intror (or_introl eq_refl)) dy Hy)
          as (dy' & Hy' & Heq_y).
        rewrite Hx', Hy'.
        cbn [Is_Some_satisfying].
        pose proof (domain_eq_PER V (model_ok:=Hm)) as Hper.
        pose proof (@PER_Symmetric _ _ Hper) as Hsym.
        pose proof (@PER_Transitive _ _ Hper) as Htrans.
        exact (Htrans _ _ _ (Htrans _ _ _ (Hsym _ _ Heq_x) Hc) Heq_y).
      + (* atom_clause a; clause_vars V V (atom_clause a) = atom_ret a :: atom_args a *)
        unfold clause_sound_for_model, atom_sound_for_model in *.
        destruct (list_Mmap (map.get i) (atom_args a)) as [iargs|] eqn:Hmm.
        2: { cbn [Is_Some_satisfying] in Hc. contradiction. }
        cbn [Is_Some_satisfying] in Hc.
        destruct (map.get i (atom_ret a)) as [iret|] eqn:Hret.
        2: { cbn [Is_Some_satisfying] in Hc. contradiction. }
        cbn [Is_Some_satisfying] in Hc.
        destruct (list_Mmap_get_setoid m i a' (atom_args a)
                    (fun k Hk => Hcompat (atom_clause a) (in_eq _ _) k
                                   (or_intror Hk))
                    iargs Hmm)
          as (a'args & Ha'args & Hall2).
        destruct (Hcompat (atom_clause a) (in_eq _ _) (atom_ret a)
                    (or_introl eq_refl) iret Hret)
          as (a'ret & Hret' & Heq_ret).
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
    Local Notation atom_node :=
      (@Theorems.atom_node V V_Eqb V_default V_map V_trie X).

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
          /\ args_in_instance l (map snd sg) i2 (map snd sub)
          /\ (exists i1,
                egraph_sound_for_interpretation (lang_model l) i1 e_assum
                /\ map.extends i2 i1).
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
      - split.
        + exact Hai2.
        + exact (ex_intro _ i1 (conj Hsnd_assum Hext12)).
    Qed.

    (* ===== Lemma 1: generic projection from egraph_sound_for_interpretation ===== *)
    Lemma egraph_atoms_sound (i : V_map (domain V (lang_model l))) (e : instance)
        (Hsnd : egraph_sound_for_interpretation (lang_model l) i e)
      : forall al, atom_in_egraph al e -> atom_sound_for_model V V V_map (lang_model l) i al.
    Proof.
      intros al Hin.
      assert (Hin' : In al (db_to_atoms (db e))).
      { apply (proj2 (in_db_to_atoms_iff_atom_in_db V V_Eqb V_Eqb_ok lt succ V_default
                        V V_Eqb V_Eqb_ok V_map V_map_ok V_trie V_trie_ok al (db e))).
        exact Hin. }
      exact (in_all _ _ _
        (@QueryOptSound.db_to_atoms_sound V V_Eqb V_Eqb_ok lt succ V_default
           V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_trie V_trie_ok (lang_model l) i e Hsnd)
        (in_map (@atom_clause V V) _ _ Hin')).
    Qed.

    (* ===== Lemma 3: conclusion_i2_sound_assum ===== *)
    Lemma conclusion_i2_sound_assum name c args t (sg : subst)
        (Hin : In (name, term_rule c args t) l)
        (Hsg : wf_subst l [] sg c)
      : let sub    := fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)) in
        let e_assum := snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))) in
        let e_concl := snd (force_equiv V V_Eqb V V_map V_map V_trie (X:=X)
                              (snd (rebuild rf (snd (add_open_term succ sort_of l true false sub
                                 (con name (id_args c)) e_assum))))) in
        exists i2,
          egraph_sound_for_interpretation (lang_model l) i2 e_concl
          /\ args_in_instance l (map snd sg) i2 (map snd sub)
          /\ (forall al, atom_in_egraph al e_assum ->
                atom_sound_for_model V V V_map (lang_model l) i2 al).
    Proof.
      cbn zeta.
      pose proof (conclusion_egraph_sound name c args t sg Hin Hsg) as H.
      cbn zeta in H.
      destruct H as (i2 & Hsnd_concl & Hai2 & i1 & Hsnd_i1 & Hext12).
      exists i2.
      split; [exact Hsnd_concl|].
      split; [exact Hai2|].
      intros al Hin_al.
      exact (QueryOptSound.atom_sound_extend V lt succ V_default V V_map (lang_model l)
               i1 i2 al Hext12 (egraph_atoms_sound i1 _ Hsnd_i1 al Hin_al)).
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

    (* Sort version of atom_tree_deq: one scon layer over atom_tree_deq. *)
    Lemma atom_tree_sort_deq
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
      : forall ts, wf_sort l cc ts -> forall xs,
          atom_tree_sort eF sub ts xs ->
          exists d1 d2, map.get j1 xs = Some d1
                     /\ map.get j2 xs = Some d2
                     /\ domain_eq V (lang_model l) d1 d2.
    Proof.
      intros [n s] Hws xs Htree.
      assert (IHsall : all (fun e => forall t, wf_term l cc e t -> forall xe,
                 atom_tree eF sub e xe ->
                 exists d1 d2, map.get j1 xe = Some d1
                            /\ map.get j2 xe = Some d2
                            /\ domain_eq V (lang_model l) d1 d2) s).
      { clear Hws Htree xs n.
        induction s as [|e0 s0 IH]; cbn; [exact I|]. split; [|exact IH].
        intros t0 Hwt0 xe0 Htree0.
        exact (atom_tree_deq j1 j2 eF sub cc Hsnd1 Hsnd2 Hleaf Hdom e0 t0 Hwt0 xe0 Htree0). }
      unfold Theorems.atom_tree_sort in Htree.
      destruct Htree as (sids & Htrees & Hatom).
      safe_invert Hws.
      match goal with
        Hwfa : Model.wf_args _ s ?c'0 |- _ =>
          destruct (atom_tree_args_deq j1 j2 eF sub cc c'0 Hsnd1 Hsnd2 Hleaf Hdom
                      s Hwfa IHsall sids Htrees) as (d1s & d2s & Hm1 & Hm2 & Hds)
      end.
      pose proof (Hsnd1 _ Hatom) as Hsa1.
      pose proof (Hsnd2 _ Hatom) as Hsa2.
      unfold atom_sound_for_model in Hsa1, Hsa2.
      cbn [atom_args atom_ret atom_fn] in Hsa1, Hsa2.
      rewrite Hm1 in Hsa1. cbn [Is_Some_satisfying] in Hsa1.
      rewrite Hm2 in Hsa2. cbn [Is_Some_satisfying] in Hsa2.
      destruct (map.get j1 xs) as [out1|] eqn:Ho1;
        [| cbn [Is_Some_satisfying] in Hsa1; contradiction].
      destruct (map.get j2 xs) as [out2|] eqn:Ho2;
        [| cbn [Is_Some_satisfying] in Hsa2; contradiction].
      cbn [Is_Some_satisfying] in Hsa1, Hsa2.
      exists out1, out2. split; [reflexivity|]. split; [reflexivity|].
      pose proof (@Theorems.lang_model_ok V V_Eqb V_Eqb_ok sort_of l Hsof Hwf) as Hmok.
      exact (@interprets_to_functional V (lang_model l) Hmok n d1s d2s out1 out2 Hsa1 Hsa2 Hds).
    Qed.

    (* [atom_node] is now defined in Theorems.v (next to [atom_tree]); see the
       [Local Notation atom_node] above. *)

    (* Helper: Forall2 R s sids -> In (si,sid) (combine s sids) -> R si sid *)
    Lemma forall2_in_combine_r (A B : Type) (R : A -> B -> Prop) (s : list A) (sids : list B)
      : Forall2 R s sids ->
        forall si sid, In (si, sid) (combine s sids) -> R si sid.
    Proof.
      induction 1 as [|x y s' sids' HR HF2 IH]; intros si sid HIn.
      - cbn in HIn. destruct HIn.
      - cbn in HIn. destruct HIn as [Heq | HIn].
        + injection Heq as <- <-. exact HR.
        + exact (IH si sid HIn).
    Qed.

    (* Helper: each element of wf_args s has a wf_term *)
    Lemma wf_args_in_wf_term (cc c' : ctx) (s : list term)
        (Hwfa : wf_args l cc s c')
      : all (fun e => exists t, wf_term l cc e t) s.
    Proof.
      induction Hwfa as [| c'' s' IHwfa name e0 t Hwft IH].
      - exact I.
      - cbn. split.
        + eexists. eassumption.
        + exact IH.
    Qed.

    (* Helper: In k sids -> length s = length sids -> exists si, In (si,k) (combine s sids) *)
    Lemma in_list_exists_pair (A B : Type) (s : list A) (sids : list B) (k : B)
        (Hlen : length s = length sids)
        (Hk : In k sids)
      : exists si, In (si, k) (combine s sids).
    Proof.
      revert sids Hlen Hk.
      induction s as [| e s' IH]; intros sids Hlen Hk.
      - destruct sids; cbn in *; [destruct Hk | discriminate].
      - destruct sids as [| sid sids']; cbn in Hlen; [discriminate|].
        injection Hlen as Hlen'.
        cbn in Hk. destruct Hk as [Heq | Hk].
        + subst sid. exists e. cbn. left. reflexivity.
        + destruct (IH sids' Hlen' Hk) as [si Hsi].
          exists si. cbn. right. exact Hsi.
    Qed.

    (* Every id appearing in an atom_node's atom (ret or args) is covered:
       it is the root of an atom_tree of some wf subterm. *)
    Lemma atom_node_covered (eF : instance) (sub : named_list V) (cc : ctx)
      : forall e t, wf_term l cc e t -> forall xe,
          atom_tree eF sub e xe ->
          forall a, atom_node eF sub e xe a ->
            a.(atom_fn) <> sort_of
            /\ (forall k, In k (a.(atom_ret) :: a.(atom_args)) ->
                  exists e' t', wf_term l cc e' t' /\ atom_tree eF sub e' k).
    Proof.
      intro e; induction e as [x | n s IHs] using term_ind; intros t Hwt xe Htree a Hnode.
      - inversion Hnode.
      - safe_invert Htree.
        apply WfCutElim.invert_wf_term_con in Hwt.
        destruct Hwt as (c'0 & args0 & t' & Hin & Hwfa & _).
        assert (IHsall : all (fun e => forall t, wf_term l cc e t -> forall xe,
                   atom_tree eF sub e xe ->
                   forall a, atom_node eF sub e xe a ->
                     a.(atom_fn) <> sort_of
                     /\ forall k, In k (a.(atom_ret) :: a.(atom_args)) ->
                           exists e' t', wf_term l cc e' t' /\ atom_tree eF sub e' k) s).
        { clear -IHs. induction s as [|e0 s0 IH]; cbn; [exact I|].
          destruct IHs as [IHe0 IHs0]. split; [exact IHe0 | exact (IH IHs0)]. }
        pose proof (wf_args_in_wf_term cc c'0 s Hwfa) as Hwfs.
        match goal with
          Htrees : Forall2 (atom_tree eF sub) s ?sids,
          Hatom : atom_in_egraph (Build_atom n ?sids xe) eF |- _ =>
            rename Htrees into Htrees_orig; rename Hatom into Hatom_orig
        end.
        inversion Hnode; subst.
        + (* an_root *)
          cbn [atom_fn atom_ret atom_args].
          split.
          * intro Heq. apply Hsof. rewrite <- Heq.
            eapply pair_fst_in. exact Hin.
          * intros k Hk.
            destruct Hk as [Hk | Hk].
            -- subst k.
               exists (con n s), (t' [/with_names_from c'0 s/]).
               split.
               ++ eapply wf_term_by; eassumption.
               ++ eapply at_con; eassumption.
            -- rename H1 into HF2_0. rename H4 into Hatom0.
               pose proof (Forall2_length HF2_0) as Hlen.
               destruct (in_list_exists_pair _ _ s _ k Hlen Hk) as [si Hsi].
               pose proof (in_combine_l s _ si k Hsi) as Hin_si.
               pose proof (forall2_in_combine_r _ _ (atom_tree eF sub) s _ HF2_0 si k Hsi)
                 as Htree_si.
               pose proof (in_all _ _ _ Hwfs Hin_si) as [t_si Hwft_si].
               exists si, t_si.
               split; [exact Hwft_si | exact Htree_si].
        + (* an_sub *)
          rename H1 into HF2_0. rename H3 into Hcomb. rename H6 into Hnode'.
          pose proof (in_combine_l s _ si sid Hcomb) as Hin_si.
          pose proof (forall2_in_combine_r _ _ (atom_tree eF sub) s _ HF2_0 si sid Hcomb)
            as Htree_si.
          pose proof (in_all _ _ _ Hwfs Hin_si) as [t_si Hwft_si].
          pose proof (in_all _ _ _ IHsall Hin_si) as IHsi.
          exact (IHsi t_si Hwft_si sid Htree_si a Hnode').
    Qed.

    (* Sort-level wrapper of [atom_node_covered]: the assumption-coverage
       frame characterizes each non-sort_of db atom as an [atom_node] of some
       ctx-var's SORT skeleton (the phantom term [con n s] of [scon n s]).
       Here [con n s] is the head of a wf_sort, not a wf_term, so the term
       lemma does not apply directly; the [an_root] top atom is covered by the
       sort itself ([scon n s]) and by the arg terms, the [an_sub] nodes by
       [atom_node_covered] on the arg terms. *)
    Lemma atom_tree_sort_node_covered (eF : instance) (sub : named_list V) (cc : ctx)
      : forall n s, wf_sort l cc (scon n s) -> forall xs,
          atom_tree_sort eF sub (scon n s) xs ->
          forall a, atom_node eF sub (con n s) xs a ->
            a.(atom_fn) <> sort_of
            /\ (forall k, In k (a.(atom_ret) :: a.(atom_args)) ->
                  (exists e t, wf_term l cc e t /\ atom_tree eF sub e k)
                \/ (exists ts, wf_sort l cc ts /\ atom_tree_sort eF sub ts k)).
    Proof.
      intros n s Hws xs Htree_sort a Hnode.
      inversion Hws; subst.
      rename H2 into Hin0. rename H3 into Hwfa0.
      unfold atom_tree_sort in Htree_sort.
      destruct Htree_sort as [sids0 Htree_sort].
      destruct Htree_sort as [HF2_sort Hatom_sort].
      pose proof (wf_args_in_wf_term cc c' s Hwfa0) as Hwfs.
      inversion Hnode; subst.
      - (* an_root: a = Build_atom n sids xs *)
        cbn [atom_fn atom_ret atom_args].
        split.
        + intro Heq. apply Hsof. rewrite <- Heq. eapply pair_fst_in. exact Hin0.
        + intros k Hk. destruct Hk as [Hk | Hk].
          * subst k. right.
            exists (scon n s). split.
            -- eapply wf_sort_by; eassumption.
            -- unfold atom_tree_sort. eexists. split; [exact H1 | exact H4].
          * left.
            pose proof (Forall2_length H1) as Hlen.
            destruct (in_list_exists_pair _ _ s _ k Hlen Hk) as [si Hsi].
            pose proof (in_combine_l s _ si k Hsi) as Hin_si.
            pose proof (forall2_in_combine_r _ _ (atom_tree eF sub) s _ H1 si k Hsi)
              as Htree_si.
            pose proof (in_all _ _ _ Hwfs Hin_si) as [t_si Hwft_si].
            exists si, t_si. split; [exact Hwft_si | exact Htree_si].
      - (* an_sub into s_i *)
        pose proof (in_combine_l s sids si sid H3) as Hin_si.
        pose proof (forall2_in_combine_r _ _ (atom_tree eF sub) s sids H1 si sid H3)
          as Htree_si.
        pose proof (in_all _ _ _ Hwfs Hin_si) as [t_si Hwft_si].
        pose proof (atom_node_covered eF sub cc si t_si Hwft_si sid Htree_si a H6)
          as [Hfn Hcov].
        split; [exact Hfn|].
        intros k Hk. left. exact (Hcov k Hk).
    Qed.

    (* ===== assumption_ids_agree: the agreement engine.  Given [a] and [i2]
       both sound on [eF]'s atoms, agreeing up to [domain_eq] on the readback
       leaves ([Hleaf]), and COVERAGE ([Hcover]: every id mapped by BOTH [a] and
       [i2] carries an [atom_tree] or [atom_tree_sort]), [a] and [i2] agree up to
       [domain_eq] wherever both are defined.  This is exactly the [Hagree]
       hypothesis consumed by [term_concl_construct].  Pure application of
       [atom_tree_deq] / [atom_tree_sort_deq] + PER symmetry; 0 new math.

       NOTE on the contract: [Hcover] is stated on the OVERLAP dom(a) ∩ dom(i2),
       not on all of [forall_vars].  This keeps the eventual confinement premise
       (R5: dom(a) ⊆ forall_vars) OUT of this lemma's statement — it is needed
       only to discharge [Hcover] (a fresh conclusion id mapped by an
       unconfined [a] would have no [atom_tree] in [eF] and break coverage). ===== *)
    Lemma assumption_ids_agree
        (a i2 : V_map (domain V (lang_model l)))
        (eF : instance) (sub : named_list V) (cc : ctx) (P : V -> Prop)
        (Hsnd_a : forall al, atom_in_egraph al eF ->
                    atom_sound_for_model V V V_map (lang_model l) a al)
        (Hsnd_i2 : forall al, atom_in_egraph al eF ->
                     atom_sound_for_model V V V_map (lang_model l) i2 al)
        (Hleaf : forall x, In x (map fst sub) ->
                   exists d1 d2,
                     map.get a  (named_list_lookup default sub x) = Some d1
                     /\ map.get i2 (named_list_lookup default sub x) = Some d2
                     /\ domain_eq V (lang_model l) d1 d2)
        (Hdom : map fst cc = map fst sub)
        (Hcover : forall k da d, P k ->
                    map.get a k = Some da -> map.get i2 k = Some d ->
                    (exists e t, wf_term l cc e t /\ atom_tree eF sub e k)
                  \/ (exists ts, wf_sort l cc ts /\ atom_tree_sort eF sub ts k))
      : forall k d da, P k -> map.get i2 k = Some d -> map.get a k = Some da ->
          domain_eq V (lang_model l) d da.
    Proof.
      intros k d da HP Hi2 Ha.
      pose proof (domain_eq_PER V
        (model_ok:=(@Theorems.lang_model_ok V V_Eqb V_Eqb_ok sort_of l Hsof Hwf)))
        as Hper.
      pose proof (@PER_Symmetric _ _ Hper) as Hsym.
      destruct (Hcover k da d HP Ha Hi2) as [ (e & t & Hwt & Htree) | (ts & Hws & Htree) ].
      - destruct (atom_tree_deq a i2 eF sub cc Hsnd_a Hsnd_i2 Hleaf Hdom e t Hwt k Htree)
          as (d1 & d2 & Ha' & Hi2' & Hdeq).
        assert (d1 = da) by congruence; assert (d2 = d) by congruence; subst d1 d2.
        exact (Hsym _ _ Hdeq).
      - destruct (atom_tree_sort_deq a i2 eF sub cc Hsnd_a Hsnd_i2 Hleaf Hdom ts Hws k Htree)
          as (d1 & d2 & Ha' & Hi2' & Hdeq).
        assert (d1 = da) by congruence; assert (d2 = d) by congruence; subst d1 d2.
        exact (Hsym _ _ Hdeq).
    Qed.

    (* ===== leaf_agree: given the faithfulness hypothesis (Hfaith) and
       args_in_instance (Hai2), every variable x in sub maps to entries
       in both a and i2 that agree up to domain_eq.  This is exactly the
       [Hleaf] hypothesis consumed by [atom_tree_deq] / [assumption_ids_agree]. ===== *)
    Lemma leaf_agree (a i2 : V_map (domain V (lang_model l))) (sg : subst)
        (cc : ctx) (sub : named_list V)
        (Hwfc : wf_ctx l cc)
        (Hsg : wf_subst l [] sg cc)
        (Hmapfst_sg : map fst sg = map fst cc)
        (Hfst_sub : map fst sub = map fst cc)
        (Hfaith : forall x, In x (map fst sub) ->
                    map.get a (named_list_lookup default sub x) = Some (inl (named_list_lookup default sg x)))
        (Hai2 : args_in_instance l (map snd sg) i2 (map snd sub))
      : forall x, In x (map fst sub) ->
          exists d1 d2,
            map.get a  (named_list_lookup default sub x) = Some d1
            /\ map.get i2 (named_list_lookup default sub x) = Some d2
            /\ domain_eq V (lang_model l) d1 d2.
    Proof.
      intros x Hx.
      pose proof (wf_ctx_all_fresh Hwfc) as Hafc.
      assert (Hafsub : all_fresh sub) by
        (apply NoDup_fresh; rewrite Hfst_sub; apply NoDup_fresh; exact Hafc).
      assert (Hafsg : all_fresh sg) by
        (apply NoDup_fresh; rewrite Hmapfst_sg; apply NoDup_fresh; exact Hafc).
      (* Helper: named_list_lookup default l x = v when all_fresh l, In (x,v) l *)
      assert (Hlk_sub : forall v, In (x, v) sub -> named_list_lookup default sub x = v).
      { intros v Hv.
        clear -V_Eqb_ok Hafsub Hv.
        induction sub as [| [m w] sub' IH]; cbn in *; [tauto|].
        destruct Hafsub as [Hfr Hafsub'].
        destruct Hv as [Heq | Hv'].
        - inversion Heq; subst m w. eqb_case x x; congruence.
        - eqb_case x m.
          + exfalso. apply Hfr. apply pair_fst_in with (a:=v). exact Hv'.
          + apply IH; auto. }
      assert (Hlk_sg : forall e, In (x, e) sg -> named_list_lookup default sg x = e).
      { intros e He.
        clear -V_Eqb_ok Hafsg He.
        induction sg as [| [m w] sg' IH]; cbn in *; [tauto|].
        destruct Hafsg as [Hfr Hafsg'].
        destruct He as [Heq | He'].
        - inversion Heq; subst m w. eqb_case x x; congruence.
        - eqb_case x m.
          + exfalso. apply Hfr. apply pair_fst_in with (a:=e). exact He'.
          + apply IH; auto. }
      destruct (pair_fst_in_exists sub x Hx) as [v_sub Hv_sub].
      assert (Hx_sg : In x (map fst sg)) by
        (rewrite Hmapfst_sg; rewrite <- Hfst_sub; exact Hx).
      destruct (pair_fst_in_exists sg x Hx_sg) as [e_sg He_sg].
      (* with_names_from cc (map snd sg) = sg *)
      assert (Heq_subst : with_names_from cc (map snd sg) = sg).
      { pose proof (wf_subst_dom_eq Hsg) as Hdom.
        revert Hdom. clear -sg cc. revert sg.
        induction cc as [|[n0 t0] cc_rest IH]; destruct sg as [|[n1 e1] sg_rest];
          cbn; intros Hdom; auto; try discriminate.
        inversion Hdom; subst. f_equal. apply IH. exact H1. }
      assert (Hin_sg_wn : In (x, e_sg) (with_names_from cc (map snd sg))).
      { rewrite Heq_subst. exact He_sg. }
      assert (Hin_sub_eq : In (x, v_sub) sub) by exact Hv_sub.
      (* i2 side: use args_in_instance_in *)
      pose proof (@Theorems.args_in_instance_in V V_Eqb V_Eqb_ok V_map sort_of l
                    (map snd sg) i2 cc x e_sg v_sub sub Hai2
                    (@Theorems.wf_args_from_wf_subst V V_Eqb l [] sg cc Hsg)
                    (eq_sym Hfst_sub) Hafc Hin_sg_wn Hin_sub_eq) as Haii.
      destruct Haii as [d2 Hd2].
      destruct Hd2 as [Hgd2 Hdeq2].
      (* Rewrite sub-lookups *)
      rewrite (Hlk_sub v_sub Hv_sub).
      pose proof (Hfaith x Hx) as Hga.
      rewrite (Hlk_sub v_sub Hv_sub) in Hga.
      rewrite (Hlk_sg e_sg He_sg) in Hga.
      exists (inl e_sg : domain V (lang_model l)), d2.
      split; [exact Hga|].
      split; [exact Hgd2|].
      (* domain_eq V (lang_model l) (inl e_sg) d2 from lang_model_eq l d2 (inl e_sg) via PER symmetry *)
      pose proof (domain_eq_PER V
        (model_ok:=(@Theorems.lang_model_ok V V_Eqb V_Eqb_ok sort_of l Hsof Hwf)))
        as Hper.
      pose proof (@PER_Symmetric _ _ Hper) as Hsym.
      exact (Hsym _ _ Hdeq2).
    Qed.

    (* ===== R4 assembly core (pure plumbing): given the canonical interp i2
       sound on all seq_conclusions clauses, well-formed, and AGREEING with the
       adversary a wherever both are defined ON CONCLUSION VARS, build
       a' := putmany i2 a (a wins), which extends a and is sound on the
       conclusions (via all_clause_sound_setoid). ===== *)
    Lemma term_concl_construct (a i2 : V_map (domain V (lang_model l)))
        name c args t
        (Hwf_i2 : forall k d, map.get i2 k = Some d -> domain_eq V (lang_model l) d d)
        (Hclauses : all (clause_sound_for_model V V V_map (lang_model l) i2)
                      (seq_conclusions (@rule_to_log_rule V V_Eqb V_default V_map V_trie
                                          succ sort_of l X HX rf name (term_rule c args t))))
        (Hagree : forall cl, In cl (seq_conclusions (@rule_to_log_rule V V_Eqb V_default V_map V_trie
                                          succ sort_of l X HX rf name (term_rule c args t))) ->
                    forall k, In k (clause_vars V V cl) ->
                    forall d da, map.get i2 k = Some d -> map.get a k = Some da ->
                      domain_eq V (lang_model l) d da)
      : exists a' : V_map (domain V (lang_model l)),
          map.extends a' a /\
          all (clause_sound_for_model V V V_map (lang_model l) a')
            (seq_conclusions (@rule_to_log_rule V V_Eqb V_default V_map V_trie
                                succ sort_of l X HX rf name (term_rule c args t))).
    Proof.
      exists (map.putmany i2 a).
      split.
      - intros k v Hv.
        exact (@Properties.map.get_putmany_right V (domain V (lang_model l))
                 (V_map _) (V_map_ok _) _ (@eqb_boolspec V V_Eqb V_Eqb_ok) i2 a k v Hv).
      - eapply all_clause_sound_setoid;
          [ exact (@Theorems.lang_model_ok V V_Eqb V_Eqb_ok sort_of l Hsof Hwf) | | exact Hclauses ].
        intros cl Hcl k Hk d Hk_get.
        destruct (map.get a k) as [da|] eqn:Hak.
        + exists da. split.
          * exact (@Properties.map.get_putmany_right V (domain V (lang_model l))
                     (V_map _) (V_map_ok _) _ (@eqb_boolspec V V_Eqb V_Eqb_ok) i2 a k da Hak).
          * exact (Hagree cl Hcl k Hk d da Hk_get Hak).
        + exists d. split.
          * rewrite (@Properties.map.get_putmany_left V (domain V (lang_model l))
                       (V_map _) (V_map_ok _) _ (@eqb_boolspec V V_Eqb V_Eqb_ok) i2 a k Hak).
            exact Hk_get.
          * exact (Hwf_i2 k d Hk_get).
    Qed.

    (* ===== Clean assumption-coverage lemma (now PROVEN: the term path is axiom-free) ===== *)
    (* For every id k appearing in an assumption clause var, k is covered by
       an atom_tree in the assumption egraph. *)
    Lemma assum_ids_covered name c args t
        (Hin : In (name, term_rule c args t) l)
        (Hsucc : fst (rebuild rf (snd (add_ctx succ sort_of l false false c
                                  (empty_egraph V_default X)))) = Result.Success tt)
      : forall k,
          In k (forall_vars
                  (rule_to_log_rule V_map V_trie succ sort_of l rf name (term_rule c args t))) ->
          (exists e t', wf_term l c e t'
             /\ atom_tree (snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))
                          (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))) e k)
        \/ (exists ts, wf_sort l c ts
             /\ atom_tree_sort (snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))
                               (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))) ts k).
    Proof.
      set (sub := fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))) in *.
      set (e_assum := snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))) in *.
      intros k Hk.
      (* Step A: derive wf_ctx *)
      assert (Hwfc : wf_ctx l c).
      { pose proof (rule_in_wf _ _ Hwf Hin) as Hr. rewrite app_nil_r in Hr.
        rewrite invert_wf_term_rule in Hr. destruct Hr as [Hc _]. exact Hc. }
      (* Step A: derive good_worklist *)
      pose proof (@add_ctx_good_worklist V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok
                    succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as Hgwl.
      (* Step A: derive map fst sub = map fst c from add_ctx_egraph_ok,
         using the same pattern as in AddCtxInversion.v (change + set e0 + fold). *)
      change (empty_egraph V_default X)
        with (@empty_egraph V V_default V V_map V_map V_trie X) in sub, e_assum, Hgwl, Hsucc.
      set (e0 := @empty_egraph V V_default V V_map V_map V_trie X) in sub, e_assum, Hgwl, Hsucc.
      assert (Hok0 : Semantics.egraph_ok V lt V V_map V_map V_trie X e0)
        by exact (proj1 (@Semantics.empty_sound_for_interpretation V lt succ V_default V V_map V_map_ok
                           V_map V_map_ok V_trie X (lang_model l))).
      assert (Huf0 : exists roots, union_find_ok lt (Defs.equiv e0) roots)
        by exact (ex_intro _ [] (@union_find_empty_ok V lt succ V_default V_map V_map_ok)).
      assert (Hdb0 : Theorems.db_ctx_inv V V_map V_trie sort_of X e0)
        by (intros aa Hin0; exfalso;
            unfold Semantics.atom_in_db in Hin0;
            unfold e0 in Hin0; cbn [Defs.db Defs.empty_egraph] in Hin0;
            rewrite map.get_empty in Hin0; exact Hin0).
      pose proof (@Theorems.add_ctx_egraph_ok V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok
                    succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as HE.
      unfold vc in HE.
      specialize (HE e0).
      fold sub in HE.
      specialize (HE Huf0 Hdb0 Hok0).
      destruct HE as (_ & _ & _ & Hmapfst_sub & _).
      (* Hmapfst_sub : map fst (fst (add_ctx ... e0)) = map fst c.
         Since sub = fst (add_ctx ... (empty_egraph V_default X)) and e0 = @empty_egraph ...,
         these are definitionally equal: *)
      assert (Hmapfst : map fst sub = map fst c) by exact Hmapfst_sub.
      (* Step B: reduce Hk to an egraph db atom.
         Mirror exactly the Heq_e rewrite used in model_satisfies_rule_adapter_term. *)
      unfold forall_vars in Hk.
      unfold rule_to_log_rule, sequent_of_states in Hk; cbn [seq_assumptions] in Hk;
      unfold Monad.Mbind, Monad.Mret, StateMonad.state_monad in Hk.
      assert (Heq_e :
        snd (let (x, y) := add_ctx succ sort_of l false false c (empty_egraph V_default X) in
             let (_, y0) := rebuild rf y in (x, y0))
        = snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))).
      { destruct (add_ctx succ sort_of l false false c (empty_egraph V_default X)) as [sub' e1].
        cbn [snd]. destruct (rebuild rf e1) as [r2 e2]. reflexivity. }
      rewrite Heq_e in Hk. fold e_assum in Hk.
      (* Hk : In k (flat_map clause_vars (map atom_clause (db_to_atoms (db e_assum)))) *)
      rewrite in_flat_map in Hk. destruct Hk as (cl & Hcl_in & Hk_in).
      rewrite in_map_iff in Hcl_in. destruct Hcl_in as (A & Hcl_eq & HA_in).
      subst cl.
      cbn [clause_vars] in Hk_in.
      (* HA_in : In A (db_to_atoms (db e_assum)); convert to atom_in_egraph *)
      assert (HA : @Semantics.atom_in_egraph V V V_map V_map V_trie X A e_assum).
      { apply (proj1 (in_db_to_atoms_iff_atom_in_db V V_Eqb V_Eqb_ok lt succ V_default
                        V V_Eqb V_Eqb_ok V_map V_map_ok V_trie V_trie_ok A (Defs.db e_assum))).
        exact HA_in. }
      (* Step C: case split on atom_fn A = sort_of *)
      destruct (eqb (Defs.atom_fn A) sort_of) eqn:Heqfn.
      - (* sort_of branch: Heqfn : eqb (atom_fn A) sort_of = true,
           eqb_spec gives atom_fn A = sort_of *)
        pose proof (@eqb_spec V V_Eqb V_Eqb_ok (Defs.atom_fn A) sort_of) as Hsp.
        rewrite Heqfn in Hsp.
        (* Hsp : atom_fn A = sort_of *)
        rename Hsp into Hsof_A.
        pose proof (@assum_sortof_frame_eF V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok
                      succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                      rf c Hwfc Hgwl Hsucc A HA Hsof_A) as (nm & x' & Hargs_A & Hin_sub_raw).
        (* Hin_sub_raw : In (nm, x') (fst (add_ctx ... e0)), definitionally = In (nm, x') sub *)
        assert (Hin_sub : In (nm, x') sub) by exact Hin_sub_raw.
        pose proof (@add_ctx_readback_eF V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok
                      succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                      rf c Hwfc Hgwl Hsucc) as Hrbef.
        fold sub e_assum in Hrbef.
        pose proof (@CtxReadback.ctx_readback_eF_lookup V V_Eqb V_Eqb_ok V_default V_map V_trie
                      sort_of X l Hwf
                      e_assum c sub Hwfc (eq_sym Hmapfst) Hrbef nm x' Hin_sub)
          as (t' & xs' & Hin_c' & Htree' & Hatom').
        (* Hk_in : In k (atom_ret A :: atom_args A) *)
        rewrite Hargs_A in Hk_in. cbn [In] in Hk_in.
        (* Determinism: atom_ret A = xs' *)
        assert (HA' : @Semantics.atom_in_db V V V_map V_trie X
                        (Defs.Build_atom sort_of [x'] (Defs.atom_ret A)) (Defs.db e_assum)).
        { unfold Semantics.atom_in_egraph in HA.
          destruct A as [afn aargs aret].
          cbn [Defs.atom_fn Defs.atom_args Defs.atom_ret] in Hsof_A, Hargs_A, HA.
          subst afn. inversion Hargs_A; subst aargs. exact HA. }
        assert (Hret : Defs.atom_ret A = xs').
        { unfold Semantics.atom_in_db, "<$>", Is_Some_satisfying in HA', Hatom'.
          cbn [Defs.atom_fn Defs.atom_args Defs.atom_ret] in HA'.
          unfold Semantics.atom_in_egraph in Hatom'.
          unfold Semantics.atom_in_db, "<$>", Is_Some_satisfying in Hatom'.
          cbn [Defs.atom_fn Defs.atom_args Defs.atom_ret] in Hatom'.
          destruct (map.get (Defs.db e_assum) sort_of) as [tbl|];
            cbn in HA', Hatom'; [|contradiction].
          destruct (map.get tbl [x']) as [entry|];
            cbn in HA', Hatom'; [|contradiction].
          congruence. }
        destruct Hk_in as [Hk_ret | Hk_rest].
        { (* k = atom_ret A = xs': RIGHT disjunct (sort) *)
          right.
          exists t'. split.
          * exact (@Core.in_ctx_wf V V_Eqb V_Eqb_ok l c nm t' Hwf Hwfc Hin_c').
          * rewrite <- Hk_ret, Hret. exact Htree'. }
        destruct Hk_rest as [Hk_x' | contra].
        2: { destruct contra. }
        (* k = x': LEFT disjunct (term var nm) *)
          left.
          exists (var nm), t'. split.
          * apply Core.wf_term_var. exact Hin_c'.
          * rewrite <- Hk_x'.
            assert (Hafsub : all_fresh sub).
            { apply NoDup_fresh. rewrite Hmapfst. apply NoDup_fresh.
              exact (wf_ctx_all_fresh Hwfc). }
            assert (Hlk : named_list_lookup default sub nm = x').
            { clear -V_Eqb_ok Hafsub Hin_sub.
              induction sub as [| [m w] sub' IH]; cbn in *; [contradiction|].
              destruct Hafsub as [Hfr Hafsub'].
              destruct Hin_sub as [Heq | Hin_sub'].
              - inversion Heq; subst m w. eqb_case nm nm; congruence.
              - eqb_case nm m.
                + exfalso. apply Hfr. apply pair_fst_in with (a:=x'). exact Hin_sub'.
                + apply IH; auto. }
            rewrite <- Hlk. apply (@Theorems.at_var V V_Eqb V_default V_map V_trie X e_assum sub nm).
      - (* non-sort_of branch *)
        pose proof (eqb_spec (Defs.atom_fn A) sort_of) as Hsp.
        rewrite Heqfn in Hsp.
        (* Hsp : atom_fn A <> sort_of *)
        rename Hsp into Hnsof_A.
        pose proof (@assum_db_frame_eF V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok
                      succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                      rf c Hwfc Hgwl Hsucc A HA Hnsof_A) as (x & n_x & s_x & xs_x & Hxin & Htree & Hnode).
        fold sub e_assum in Htree, Hnode.
        pose proof (@Core.in_ctx_wf V V_Eqb V_Eqb_ok l c x (scon n_x s_x) Hwf Hwfc Hxin) as Hwst.
        pose proof (atom_tree_sort_node_covered e_assum sub c n_x s_x Hwst xs_x Htree A Hnode)
          as (_ & Hcov).
        exact (Hcov k Hk_in).
    Qed.

    (* ===== Residual coverage obligation (conclusion vars only) ===== *)
    (* Now proved by threading the confinement hypothesis Hconf through
       assum_ids_covered: conclusion ids must be assumption ids (by confinement),
       and assumption ids are covered (by assum_ids_covered). *)
    Lemma Hcover_concl_term name c args t
        (a i2 : V_map (domain V (lang_model l)))
        (sg : subst) (Hin : In (name, term_rule c args t) l)
        (Hsg : wf_subst l [] sg c)
        (Hsnd_a : forall al, atom_in_egraph al
                    (snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))) ->
                    atom_sound_for_model V V V_map (lang_model l) a al)
        (Hconf : forall x, Sep.has_key x a ->
                   In x (forall_vars
                           (rule_to_log_rule V_map V_trie succ sort_of l rf name (term_rule c args t))))
        (Hsucc : fst (rebuild rf (snd (add_ctx succ sort_of l false false c
                                  (empty_egraph V_default X)))) = Result.Success tt)
      : forall k da d,
          In k (flat_map (clause_vars V V) (seq_conclusions
                   (@rule_to_log_rule V V_Eqb V_default V_map V_trie succ sort_of l
                      X HX rf name (term_rule c args t)))) ->
          map.get a k = Some da -> map.get i2 k = Some d ->
          (exists e t', wf_term l c e t'
             /\ atom_tree (snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))
                          (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))) e k)
        \/ (exists ts, wf_sort l c ts
             /\ atom_tree_sort (snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))
                               (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))) ts k).
    Proof.
      intros k da d Hk Ha Hi2k.
      apply (assum_ids_covered name c args t Hin Hsucc k).
      apply Hconf.
      unfold Sep.has_key. rewrite Ha. exact I.
    Qed.

    (* ===== (II) conclusion obligation for term rules ===== *)
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
        (Hsucc : fst (rebuild rf (snd (add_ctx succ sort_of l false false c
                                         (empty_egraph V_default X)))) = Success tt)
        (Hsnd_a : forall al, atom_in_egraph al
                    (snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))) ->
                    atom_sound_for_model V V V_map (lang_model l) a al)
        (Hconf : forall x, Sep.has_key x a ->
                   In x (forall_vars
                           (rule_to_log_rule V_map V_trie succ sort_of l rf name (term_rule c args t))))
      : exists a' : V_map (domain V (lang_model l)),
          map.extends a' a /\
          all (clause_sound_for_model V V V_map (lang_model l) a')
            (seq_conclusions (@rule_to_log_rule V V_Eqb V_default V_map V_trie succ sort_of l
                                X HX rf name (term_rule c args t))).
    Proof.
      set (sub    := fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))) in *.
      set (e_assum := snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))) in *.
      assert (Hwfc : wf_ctx l c).
      { pose proof (rule_in_wf _ _ Hwf Hin) as Hr. rewrite app_nil_r in Hr.
        rewrite invert_wf_term_rule in Hr. destruct Hr as [Hc _]. exact Hc. }
      pose proof (conclusion_i2_sound_assum name c args t sg Hin Hsg)
        as (i2 & Hsnd_concl_i2 & Hai2 & Hsnd_i2_assum).
      pose proof (concl_clauses_sound_term name c args t sg Hin Hsg i2 Hsnd_concl_i2)
        as Hclauses.
      assert (Hwf_i2 : forall k d, map.get i2 k = Some d ->
                         domain_eq V (lang_model l) d d).
      { intros k d Hk.
        exact (Semantics.idx_interpretation_wf V V V_map V_map V_trie unit (lang_model l)
                 i2 _ Hsnd_concl_i2 k d Hk). }
      pose proof (assumption_egraph_sound c Hwfc sg Hsg) as Htmp.
      destruct Htmp as (_ & i1_tmp & _ & Hfst_sub & _).
      set (P := fun k => In k (flat_map (clause_vars V V)
                    (seq_conclusions (rule_to_log_rule V_map V_trie succ sort_of l rf name
                                        (term_rule c args t))))).
      assert (Hleaf : forall x, In x (map fst sub) ->
                        exists d1 d2,
                          map.get a (named_list_lookup default sub x) = Some d1
                          /\ map.get i2 (named_list_lookup default sub x) = Some d2
                          /\ domain_eq V (lang_model l) d1 d2).
      { exact (leaf_agree a i2 sg c sub Hwfc Hsg Hmapfst Hfst_sub Hfaith Hai2). }
      assert (Hcover_res : forall k da d, P k ->
                  map.get a k = Some da -> map.get i2 k = Some d ->
                  (exists e t', wf_term l c e t' /\ atom_tree e_assum sub e k)
                \/ (exists ts, wf_sort l c ts /\ atom_tree_sort e_assum sub ts k)).
      { intros k da d HP Ha Hi2k.
        exact (Hcover_concl_term name c args t a i2 sg Hin Hsg Hsnd_a Hconf Hsucc k da d HP Ha Hi2k). }
      assert (Hagree : forall k d da, P k -> map.get i2 k = Some d ->
                  map.get a k = Some da -> domain_eq V (lang_model l) d da).
      { exact (assumption_ids_agree a i2 e_assum sub c P
                 Hsnd_a Hsnd_i2_assum Hleaf (eq_sym Hfst_sub) Hcover_res). }
      exact (term_concl_construct a i2 name c args t Hwf_i2 Hclauses
               (fun cl Hcl k Hk d da Hi2k Ha =>
                  Hagree k d da
                    (proj2 (in_flat_map (clause_vars V V)
                          (seq_conclusions (rule_to_log_rule V_map V_trie succ sort_of l rf name
                                              (term_rule c args t))) k)
                       (ex_intro _ cl (conj Hcl Hk)))
                    Hi2k Ha)).
    Qed.

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
      intros a Hkeys Hconf Hassum.
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
      exact (term_rule_concl_obligation name c args t a sg Hsg Hmapfst Hfaith Hin
               Hsucc Hsnd_atoms Hconf).
    Qed.

    (* ===== Sort conclusion: egraph sound after add_open_sort + rebuild + force_equiv ===== *)
    Lemma conclusion_egraph_sound_sort name c args (sg : subst)
        (Hin : In (name, sort_rule c args) l)
        (Hsg : wf_subst l [] sg c)
      : let sub    := fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)) in
        let e_assum := snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))) in
        let e_open  := snd (add_open_sort succ sort_of l true false sub (scon name (id_args c)) e_assum) in
        let e_concl := snd (force_equiv V V_Eqb V V_map V_map V_trie (X:=X)
                              (snd (rebuild rf e_open))) in
        exists i2,
          egraph_sound_for_interpretation (lang_model l) i2 e_concl
          /\ args_in_instance l (map snd sg) i2 (map snd sub)
          /\ (exists i1,
                egraph_sound_for_interpretation (lang_model l) i1 e_assum
                /\ map.extends i2 i1).
    Proof.
      cbn zeta.
      set (sub    := fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))).
      set (e_ctx  := snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))).
      set (e_assum := snd (rebuild rf e_ctx)).
      assert (Hwfc : wf_ctx l c).
      { pose proof (rule_in_wf _ _ Hwf Hin) as Hr. rewrite app_nil_r in Hr.
        rewrite invert_wf_sort_rule in Hr. destruct Hr as [Hc _]. exact Hc. }
      pose proof (assumption_egraph_sound c Hwfc sg Hsg)
        as (Hok_assum & i1 & Hsnd_assum & Hfst_sub & Hai1).
      assert (Hwfs : wf_sort l c (scon name (id_args c))).
      { eapply wf_sort_by; eauto.
        eapply id_args_wf; eauto with utils. }
      pose proof (@Theorems.add_open_sort_sound
                    V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok
                    succ sort_of lt lt_asymmetric lt_succ lt_trans
                    X HX l Hwf Hsof true
                    c sub (map snd sg) (scon name (id_args c))
                    (@Theorems.wf_args_from_wf_subst V V_Eqb l [] sg c Hsg)
                    Hwfc Hwfs
                    (eq_sym Hfst_sub) i1)
        as Hvc_open.
      unfold vc in Hvc_open.
      specialize (Hvc_open e_assum).
      unfold Theorems.open_sort_post in Hvc_open.
      specialize (Hvc_open Hok_assum Hsnd_assum Hai1).
      destruct Hvc_open as [i2 (Hext_open & _)].
      destruct Hext_open as (Hok_open & Hext12 & Hsnd_open & _).
      set (e_open := snd (add_open_sort succ sort_of l true false sub
                            (scon name (id_args c)) e_assum)).
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
      pose proof (@QueryOptSound.force_equiv_preserves_sound
                    V V_Eqb V_Eqb_ok lt V V_map V_map V_map_ok V_trie
                    (lang_model l) i2 e_rb2
                    (Semantics.egraph_equiv_ok V lt V V_map V_map V_trie unit e_rb2 Hok_rb2)
                    Hsnd_rb2)
        as Hsnd_concl.
      pose proof (@Theorems.args_in_instance_monotone
                    V V_Eqb V_map sort_of l (map snd sg) i1 i2
                    (map snd sub) Hext12 Hai1)
        as Hai2.
      exists i2.
      split.
      - exact Hsnd_concl.
      - split.
        + exact Hai2.
        + exact (ex_intro _ i1 (conj Hsnd_assum Hext12)).
    Qed.

    (* ===== Sort conclusion i2: i2 is also sound on assumption atoms ===== *)
    Lemma conclusion_i2_sound_assum_sort name c args (sg : subst)
        (Hin : In (name, sort_rule c args) l)
        (Hsg : wf_subst l [] sg c)
      : let sub    := fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)) in
        let e_assum := snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))) in
        let e_concl := snd (force_equiv V V_Eqb V V_map V_map V_trie (X:=X)
                              (snd (rebuild rf (snd (add_open_sort succ sort_of l true false sub
                                 (scon name (id_args c)) e_assum))))) in
        exists i2,
          egraph_sound_for_interpretation (lang_model l) i2 e_concl
          /\ args_in_instance l (map snd sg) i2 (map snd sub)
          /\ (forall al, atom_in_egraph al e_assum ->
                atom_sound_for_model V V V_map (lang_model l) i2 al).
    Proof.
      cbn zeta.
      pose proof (conclusion_egraph_sound_sort name c args sg Hin Hsg) as H.
      cbn zeta in H.
      destruct H as (i2 & Hsnd_concl & Hai2 & i1 & Hsnd_i1 & Hext12).
      exists i2.
      split; [exact Hsnd_concl|].
      split; [exact Hai2|].
      intros al Hin_al.
      exact (QueryOptSound.atom_sound_extend V lt succ V_default V V_map (lang_model l)
               i1 i2 al Hext12 (egraph_atoms_sound i1 _ Hsnd_i1 al Hin_al)).
    Qed.

    (* ===== Sort conclusion clauses: all seq_conclusions clauses sound under i2 ===== *)
    Lemma concl_clauses_sound_sort name c args (sg : subst)
        (Hin : In (name, sort_rule c args) l)
        (Hsg : wf_subst l [] sg c)
        (i2 : V_map (domain V (lang_model l)))
        (Hsnd : egraph_sound_for_interpretation (lang_model l) i2
                  (snd (force_equiv V V_Eqb V V_map V_map V_trie (X:=X)
                          (snd (rebuild rf
                            (snd (add_open_sort succ sort_of l true false
                                    (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                                    (scon name (id_args c))
                                    (snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))))))))))
      : all (clause_sound_for_model V V V_map (lang_model l) i2)
            (seq_conclusions (@rule_to_log_rule V V_Eqb V_default V_map V_trie succ sort_of l X HX rf name (sort_rule c args))).
    Proof.
      unfold rule_to_log_rule, sequent_of_states.
      cbn [seq_conclusions].
      unfold Monad.Mbind, Monad.Mret, StateMonad.state_monad.
      cbn beta iota.
      set (sub    := fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))).
      set (e_ctx  := snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))).
      set (e_assum := snd (rebuild rf e_ctx)).
      set (e_open  := snd (add_open_sort succ sort_of l true false sub (scon name (id_args c)) e_assum)).
      set (e_rb2   := snd (rebuild rf e_open)).
      set (e_concl := snd (force_equiv V V_Eqb V V_map V_map V_trie (X:=X) e_rb2)).
      change (egraph_sound_for_interpretation (lang_model l) i2 e_concl) in Hsnd.
      assert (Heq_concl :
        snd (uncurry
          (fun (a : list (V * V)) (x : instance) =>
           let (x0, y) := add_open_sort succ sort_of l true false a (scon name (id_args c)) x in
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
        destruct (add_open_sort succ sort_of l true false sub0 (scon name (id_args c)) e2) as [sub3 e3].
        cbn [fst snd].
        destruct (rebuild rf e3) as [r4 e4]. cbn [fst snd].
        destruct (force_equiv V V_Eqb V V_map V_map V_trie e4) as [r5 e5]. cbn [fst snd].
        reflexivity. }
      assert (Heq_assum :
        snd (let (x, y) := add_ctx succ sort_of l false false c (empty_egraph V_default X) in
             let (_, y0) := rebuild rf y in (x, y0)) = e_assum).
      { unfold e_assum, e_ctx.
        destruct (add_ctx succ sort_of l false false c (empty_egraph V_default X)) as [sub0 e1].
        cbn [snd fst].
        destruct (rebuild rf e1) as [r2 e2]. reflexivity. }
      rewrite Heq_concl, Heq_assum.
      apply all_app; split.
      - apply SemanticsUtil.all_map_in.
        intros p Hp.
        apply incl_filter in Hp.
        destruct p as [px py].
        pose proof (in_all _ _ _
          (@QueryOptSound.uf_eqs_sound V V_Eqb V_Eqb_ok V V_map V_map V_map_ok V_trie
             (lang_model l) i2 e_concl Hsnd)
          (in_map (fun q => @eq_clause V V (fst q) (snd q)) _ _ Hp)) as Hsp.
        cbn [uncurry fst snd] in Hsp |- *.
        exact Hsp.
      - apply SemanticsUtil.all_map_in.
        intros a0 Ha0.
        pose proof (@QueryOpt.incl_remove_atoms V V_Eqb V_Eqb_ok lt V V_Eqb V_Eqb_ok
           V_map V_map_ok V_map V_trie V_trie_ok) as Hira.
        pose proof (Hira X (db_to_atoms (db e_assum)) e_concl a0 Ha0) as Hin_concl.
        exact (in_all _ _ _
          (@QueryOptSound.db_to_atoms_sound V V_Eqb V_Eqb_ok lt succ V_default V V_Eqb V_Eqb_ok
             V_map V_map_ok V_map V_trie V_trie_ok (lang_model l) i2 e_concl Hsnd)
          (in_map (@atom_clause V V) _ _ Hin_concl)).
    Qed.

    (* ===== Sort assumption coverage (mirror of assum_ids_covered) ===== *)
    Lemma assum_ids_covered_sort name c args
        (Hin : In (name, sort_rule c args) l)
        (Hsucc : fst (rebuild rf (snd (add_ctx succ sort_of l false false c
                                  (empty_egraph V_default X)))) = Result.Success tt)
      : forall k,
          In k (forall_vars
                  (rule_to_log_rule V_map V_trie succ sort_of l rf name (sort_rule c args))) ->
          (exists e t', wf_term l c e t'
             /\ atom_tree (snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))
                          (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))) e k)
        \/ (exists ts, wf_sort l c ts
             /\ atom_tree_sort (snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))
                               (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))) ts k).
    Proof.
      set (sub := fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))) in *.
      set (e_assum := snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))) in *.
      intros k Hk.
      assert (Hwfc : wf_ctx l c).
      { pose proof (rule_in_wf _ _ Hwf Hin) as Hr. rewrite app_nil_r in Hr.
        rewrite invert_wf_sort_rule in Hr. destruct Hr as [Hc _]. exact Hc. }
      pose proof (@add_ctx_good_worklist V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok
                    succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as Hgwl.
      change (empty_egraph V_default X)
        with (@empty_egraph V V_default V V_map V_map V_trie X) in sub, e_assum, Hgwl, Hsucc.
      set (e0 := @empty_egraph V V_default V V_map V_map V_trie X) in sub, e_assum, Hgwl, Hsucc.
      assert (Hok0 : Semantics.egraph_ok V lt V V_map V_map V_trie X e0)
        by exact (proj1 (@Semantics.empty_sound_for_interpretation V lt succ V_default V V_map V_map_ok
                           V_map V_map_ok V_trie X (lang_model l))).
      assert (Huf0 : exists roots, union_find_ok lt (Defs.equiv e0) roots)
        by exact (ex_intro _ [] (@union_find_empty_ok V lt succ V_default V_map V_map_ok)).
      assert (Hdb0 : Theorems.db_ctx_inv V V_map V_trie sort_of X e0)
        by (intros aa Hin0; exfalso;
            unfold Semantics.atom_in_db in Hin0;
            unfold e0 in Hin0; cbn [Defs.db Defs.empty_egraph] in Hin0;
            rewrite map.get_empty in Hin0; exact Hin0).
      pose proof (@Theorems.add_ctx_egraph_ok V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok
                    succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as HE.
      unfold vc in HE.
      specialize (HE e0).
      fold sub in HE.
      specialize (HE Huf0 Hdb0 Hok0).
      destruct HE as (_ & _ & _ & Hmapfst_sub & _).
      assert (Hmapfst : map fst sub = map fst c) by exact Hmapfst_sub.
      unfold forall_vars in Hk.
      unfold rule_to_log_rule, sequent_of_states in Hk; cbn [seq_assumptions] in Hk;
      unfold Monad.Mbind, Monad.Mret, StateMonad.state_monad in Hk.
      assert (Heq_e :
        snd (let (x, y) := add_ctx succ sort_of l false false c (empty_egraph V_default X) in
             let (_, y0) := rebuild rf y in (x, y0))
        = snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))).
      { destruct (add_ctx succ sort_of l false false c (empty_egraph V_default X)) as [sub' e1].
        cbn [snd]. destruct (rebuild rf e1) as [r2 e2]. reflexivity. }
      rewrite Heq_e in Hk. fold e_assum in Hk.
      rewrite in_flat_map in Hk. destruct Hk as (cl & Hcl_in & Hk_in).
      rewrite in_map_iff in Hcl_in. destruct Hcl_in as (A & Hcl_eq & HA_in).
      subst cl.
      cbn [clause_vars] in Hk_in.
      assert (HA : @Semantics.atom_in_egraph V V V_map V_map V_trie X A e_assum).
      { apply (proj1 (in_db_to_atoms_iff_atom_in_db V V_Eqb V_Eqb_ok lt succ V_default
                        V V_Eqb V_Eqb_ok V_map V_map_ok V_trie V_trie_ok A (Defs.db e_assum))).
        exact HA_in. }
      destruct (eqb (Defs.atom_fn A) sort_of) eqn:Heqfn.
      - pose proof (@eqb_spec V V_Eqb V_Eqb_ok (Defs.atom_fn A) sort_of) as Hsp.
        rewrite Heqfn in Hsp.
        rename Hsp into Hsof_A.
        pose proof (@assum_sortof_frame_eF V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok
                      succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                      rf c Hwfc Hgwl Hsucc A HA Hsof_A) as (nm & x' & Hargs_A & Hin_sub_raw).
        assert (Hin_sub : In (nm, x') sub) by exact Hin_sub_raw.
        pose proof (@add_ctx_readback_eF V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok
                      succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                      rf c Hwfc Hgwl Hsucc) as Hrbef.
        fold sub e_assum in Hrbef.
        pose proof (@CtxReadback.ctx_readback_eF_lookup V V_Eqb V_Eqb_ok V_default V_map V_trie
                      sort_of X l Hwf
                      e_assum c sub Hwfc (eq_sym Hmapfst) Hrbef nm x' Hin_sub)
          as (t' & xs' & Hin_c' & Htree' & Hatom').
        rewrite Hargs_A in Hk_in. cbn [In] in Hk_in.
        assert (HA' : @Semantics.atom_in_db V V V_map V_trie X
                        (Defs.Build_atom sort_of [x'] (Defs.atom_ret A)) (Defs.db e_assum)).
        { unfold Semantics.atom_in_egraph in HA.
          destruct A as [afn aargs aret].
          cbn [Defs.atom_fn Defs.atom_args Defs.atom_ret] in Hsof_A, Hargs_A, HA.
          subst afn. inversion Hargs_A; subst aargs. exact HA. }
        assert (Hret : Defs.atom_ret A = xs').
        { unfold Semantics.atom_in_db, "<$>", Is_Some_satisfying in HA', Hatom'.
          cbn [Defs.atom_fn Defs.atom_args Defs.atom_ret] in HA'.
          unfold Semantics.atom_in_egraph in Hatom'.
          unfold Semantics.atom_in_db, "<$>", Is_Some_satisfying in Hatom'.
          cbn [Defs.atom_fn Defs.atom_args Defs.atom_ret] in Hatom'.
          destruct (map.get (Defs.db e_assum) sort_of) as [tbl|];
            cbn in HA', Hatom'; [|contradiction].
          destruct (map.get tbl [x']) as [entry|];
            cbn in HA', Hatom'; [|contradiction].
          congruence. }
        destruct Hk_in as [Hk_ret | Hk_rest].
        { right.
          exists t'. split.
          * exact (@Core.in_ctx_wf V V_Eqb V_Eqb_ok l c nm t' Hwf Hwfc Hin_c').
          * rewrite <- Hk_ret, Hret. exact Htree'. }
        destruct Hk_rest as [Hk_x' | contra].
        2: { destruct contra. }
        left.
        exists (var nm), t'. split.
        * apply Core.wf_term_var. exact Hin_c'.
        * rewrite <- Hk_x'.
          assert (Hafsub : all_fresh sub).
          { apply NoDup_fresh. rewrite Hmapfst. apply NoDup_fresh.
            exact (wf_ctx_all_fresh Hwfc). }
          assert (Hlk : named_list_lookup default sub nm = x').
          { clear -V_Eqb_ok Hafsub Hin_sub.
            induction sub as [| [m w] sub' IH]; cbn in *; [contradiction|].
            destruct Hafsub as [Hfr Hafsub'].
            destruct Hin_sub as [Heq | Hin_sub'].
            - inversion Heq; subst m w. eqb_case nm nm; congruence.
            - eqb_case nm m.
              + exfalso. apply Hfr. apply pair_fst_in with (a:=x'). exact Hin_sub'.
              + apply IH; auto. }
          rewrite <- Hlk. apply (@Theorems.at_var V V_Eqb V_default V_map V_trie X e_assum sub nm).
      - pose proof (eqb_spec (Defs.atom_fn A) sort_of) as Hsp.
        rewrite Heqfn in Hsp.
        rename Hsp into Hnsof_A.
        pose proof (@assum_db_frame_eF V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok
                      succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                      rf c Hwfc Hgwl Hsucc A HA Hnsof_A) as (x & n_x & s_x & xs_x & Hxin & Htree & Hnode).
        fold sub e_assum in Htree, Hnode.
        pose proof (@Core.in_ctx_wf V V_Eqb V_Eqb_ok l c x (scon n_x s_x) Hwf Hwfc Hxin) as Hwst.
        pose proof (atom_tree_sort_node_covered e_assum sub c n_x s_x Hwst xs_x Htree A Hnode)
          as (_ & Hcov).
        exact (Hcov k Hk_in).
    Qed.

    (* ===== Sort conclusion coverage (mirror of Hcover_concl_term) ===== *)
    Lemma Hcover_concl_sort name c args
        (a i2 : V_map (domain V (lang_model l)))
        (sg : subst) (Hin : In (name, sort_rule c args) l)
        (Hsg : wf_subst l [] sg c)
        (Hsnd_a : forall al, atom_in_egraph al
                    (snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))) ->
                    atom_sound_for_model V V V_map (lang_model l) a al)
        (Hconf : forall x, Sep.has_key x a ->
                   In x (forall_vars
                           (rule_to_log_rule V_map V_trie succ sort_of l rf name (sort_rule c args))))
        (Hsucc : fst (rebuild rf (snd (add_ctx succ sort_of l false false c
                                  (empty_egraph V_default X)))) = Result.Success tt)
      : forall k da d,
          In k (flat_map (clause_vars V V) (seq_conclusions
                   (@rule_to_log_rule V V_Eqb V_default V_map V_trie succ sort_of l
                      X HX rf name (sort_rule c args)))) ->
          map.get a k = Some da -> map.get i2 k = Some d ->
          (exists e t', wf_term l c e t'
             /\ atom_tree (snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))
                          (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))) e k)
        \/ (exists ts, wf_sort l c ts
             /\ atom_tree_sort (snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))
                               (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))) ts k).
    Proof.
      intros k da d Hk Ha Hi2k.
      apply (assum_ids_covered_sort name c args Hin Hsucc k).
      apply Hconf.
      unfold Sep.has_key. rewrite Ha. exact I.
    Qed.

    (* ===== Sort conclusion construct (mirror of term_concl_construct) ===== *)
    Lemma sort_concl_construct (a i2 : V_map (domain V (lang_model l)))
        name c args
        (Hwf_i2 : forall k d, map.get i2 k = Some d -> domain_eq V (lang_model l) d d)
        (Hclauses : all (clause_sound_for_model V V V_map (lang_model l) i2)
                      (seq_conclusions (@rule_to_log_rule V V_Eqb V_default V_map V_trie
                                          succ sort_of l X HX rf name (sort_rule c args))))
        (Hagree : forall cl, In cl (seq_conclusions (@rule_to_log_rule V V_Eqb V_default V_map V_trie
                                          succ sort_of l X HX rf name (sort_rule c args))) ->
                    forall k, In k (clause_vars V V cl) ->
                    forall d da, map.get i2 k = Some d -> map.get a k = Some da ->
                      domain_eq V (lang_model l) d da)
      : exists a' : V_map (domain V (lang_model l)),
          map.extends a' a /\
          all (clause_sound_for_model V V V_map (lang_model l) a')
            (seq_conclusions (@rule_to_log_rule V V_Eqb V_default V_map V_trie
                                succ sort_of l X HX rf name (sort_rule c args))).
    Proof.
      exists (map.putmany i2 a).
      split.
      - intros k v Hv.
        exact (@Properties.map.get_putmany_right V (domain V (lang_model l))
                 (V_map _) (V_map_ok _) _ (@eqb_boolspec V V_Eqb V_Eqb_ok) i2 a k v Hv).
      - eapply all_clause_sound_setoid;
          [ exact (@Theorems.lang_model_ok V V_Eqb V_Eqb_ok sort_of l Hsof Hwf) | | exact Hclauses ].
        intros cl Hcl k Hk d Hk_get.
        destruct (map.get a k) as [da|] eqn:Hak.
        + exists da. split.
          * exact (@Properties.map.get_putmany_right V (domain V (lang_model l))
                     (V_map _) (V_map_ok _) _ (@eqb_boolspec V V_Eqb V_Eqb_ok) i2 a k da Hak).
          * exact (Hagree cl Hcl k Hk d da Hk_get Hak).
        + exists d. split.
          * rewrite (@Properties.map.get_putmany_left V (domain V (lang_model l))
                       (V_map _) (V_map_ok _) _ (@eqb_boolspec V V_Eqb V_Eqb_ok) i2 a k Hak).
            exact Hk_get.
          * exact (Hwf_i2 k d Hk_get).
    Qed.

    (* ===== (II) conclusion obligation for sort rules ===== *)
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
        (Hsucc : fst (rebuild rf (snd (add_ctx succ sort_of l false false c
                                         (empty_egraph V_default X)))) = Success tt)
        (Hsnd_a : forall al, atom_in_egraph al
                    (snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))) ->
                    atom_sound_for_model V V V_map (lang_model l) a al)
        (Hconf : forall x, Sep.has_key x a ->
                   In x (forall_vars
                           (rule_to_log_rule V_map V_trie succ sort_of l rf name (sort_rule c args))))
      : exists a' : V_map (domain V (lang_model l)),
          map.extends a' a /\
          all (clause_sound_for_model V V V_map (lang_model l) a')
            (seq_conclusions (@rule_to_log_rule V V_Eqb V_default V_map V_trie succ sort_of l
                                X HX rf name (sort_rule c args))).
    Proof.
      set (sub    := fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))) in *.
      set (e_assum := snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))) in *.
      assert (Hwfc : wf_ctx l c).
      { pose proof (rule_in_wf _ _ Hwf Hin) as Hr. rewrite app_nil_r in Hr.
        rewrite invert_wf_sort_rule in Hr. destruct Hr as [Hc _]. exact Hc. }
      pose proof (conclusion_i2_sound_assum_sort name c args sg Hin Hsg)
        as (i2 & Hsnd_concl_i2 & Hai2 & Hsnd_i2_assum).
      pose proof (concl_clauses_sound_sort name c args sg Hin Hsg i2 Hsnd_concl_i2)
        as Hclauses.
      assert (Hwf_i2 : forall k d, map.get i2 k = Some d ->
                         domain_eq V (lang_model l) d d).
      { intros k d Hk.
        exact (Semantics.idx_interpretation_wf V V V_map V_map V_trie unit (lang_model l)
                 i2 _ Hsnd_concl_i2 k d Hk). }
      pose proof (assumption_egraph_sound c Hwfc sg Hsg) as Htmp.
      destruct Htmp as (_ & i1_tmp & _ & Hfst_sub & _).
      set (P := fun k => In k (flat_map (clause_vars V V)
                    (seq_conclusions (rule_to_log_rule V_map V_trie succ sort_of l rf name
                                        (sort_rule c args))))).
      assert (Hleaf : forall x, In x (map fst sub) ->
                        exists d1 d2,
                          map.get a (named_list_lookup default sub x) = Some d1
                          /\ map.get i2 (named_list_lookup default sub x) = Some d2
                          /\ domain_eq V (lang_model l) d1 d2).
      { exact (leaf_agree a i2 sg c sub Hwfc Hsg Hmapfst Hfst_sub Hfaith Hai2). }
      assert (Hcover_res : forall k da d, P k ->
                  map.get a k = Some da -> map.get i2 k = Some d ->
                  (exists e t', wf_term l c e t' /\ atom_tree e_assum sub e k)
                \/ (exists ts, wf_sort l c ts /\ atom_tree_sort e_assum sub ts k)).
      { intros k da d HP Ha Hi2k.
        exact (Hcover_concl_sort name c args a i2 sg Hin Hsg Hsnd_a Hconf Hsucc k da d HP Ha Hi2k). }
      assert (Hagree : forall k d da, P k -> map.get i2 k = Some d ->
                  map.get a k = Some da -> domain_eq V (lang_model l) d da).
      { exact (assumption_ids_agree a i2 e_assum sub c P
                 Hsnd_a Hsnd_i2_assum Hleaf (eq_sym Hfst_sub) Hcover_res). }
      exact (sort_concl_construct a i2 name c args Hwf_i2 Hclauses
               (fun cl Hcl k Hk d da Hi2k Ha =>
                  Hagree k d da
                    (proj2 (in_flat_map (clause_vars V V)
                          (seq_conclusions (rule_to_log_rule V_map V_trie succ sort_of l rf name
                                              (sort_rule c args))) k)
                       (ex_intro _ cl (conj Hcl Hk)))
                    Hi2k Ha)).
    Qed.

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
      intros a Hkeys Hconf Hassum.
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
      exact (sort_rule_concl_obligation name c args a sg Hsg Hmapfst Hfaith Hin
               Hsucc Hsnd_atoms Hconf).
    Qed.

    (* ===== central obligation (bridge piece): the OPTIMIZED sequent of a
       term rule is satisfied by lang_model, composing the term adapter with
       optimize_sequent_forward_atoms.  This is the per-rule msr fact the
       downstream [compiled_rules_run1iter_rule_hyps] consumes. ===== *)
    Lemma central_obligation_term name c args t
        (Hin : In (name, term_rule c args t) l)
        (Hsucc : fst (rebuild rf (snd (add_ctx succ sort_of l false false c
                                         (empty_egraph V_default X)))) = Success tt)
      : model_satisfies_rule V V V_map (lang_model l)
          (QueryOpt.optimize_sequent V V_Eqb succ V_default V V_map V_map V_trie
             (@rule_to_log_rule V V_Eqb V_default V_map V_trie succ sort_of l
                X HX rf name (term_rule c args t)) rf).
    Proof.
      apply (@optimize_sequent_forward_atoms V V_Eqb V_Eqb_ok lt succ V_default
               V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
               (@rule_to_log_rule V V_Eqb V_default V_map V_trie succ sort_of l
                  X HX rf name (term_rule c args t)) rf (lang_model l)
               (@Theorems.lang_model_ok V V_Eqb V_Eqb_ok sort_of l Hsof Hwf)
               lt_asymmetric lt_succ lt_trans
               (db_to_atoms (db (snd (rebuild rf (snd (add_ctx succ sort_of l false false c
                                                         (empty_egraph V_default X)))))))).
      - cbn;
        destruct (add_ctx succ sort_of l false false c (empty_egraph V_default X)) as [sub e1];
        cbn [snd];
        destruct (rebuild rf e1) as [r2 e2]; reflexivity.
      - apply (@db_to_atoms_NoDup_fn_args V V_Eqb V_Eqb_ok V V_Eqb V_Eqb_ok V_map V_map_ok V_trie V_trie_ok).
      - exact (model_satisfies_rule_adapter_term name c args t Hin Hsucc).
    Qed.

    (* ===== central obligation: sort rule (mirror of the term version) ===== *)
    Lemma central_obligation_sort name c args
        (Hin : In (name, sort_rule c args) l)
        (Hsucc : fst (rebuild rf (snd (add_ctx succ sort_of l false false c
                                         (empty_egraph V_default X)))) = Success tt)
      : model_satisfies_rule V V V_map (lang_model l)
          (QueryOpt.optimize_sequent V V_Eqb succ V_default V V_map V_map V_trie
             (@rule_to_log_rule V V_Eqb V_default V_map V_trie succ sort_of l
                X HX rf name (sort_rule c args)) rf).
    Proof.
      apply (@optimize_sequent_forward_atoms V V_Eqb V_Eqb_ok lt succ V_default
               V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
               (@rule_to_log_rule V V_Eqb V_default V_map V_trie succ sort_of l
                  X HX rf name (sort_rule c args)) rf (lang_model l)
               (@Theorems.lang_model_ok V V_Eqb V_Eqb_ok sort_of l Hsof Hwf)
               lt_asymmetric lt_succ lt_trans
               (db_to_atoms (db (snd (rebuild rf (snd (add_ctx succ sort_of l false false c
                                                         (empty_egraph V_default X)))))))).
      - cbn;
        destruct (add_ctx succ sort_of l false false c (empty_egraph V_default X)) as [sub e1];
        cbn [snd];
        destruct (rebuild rf e1) as [r2 e2]; reflexivity.
      - apply (@db_to_atoms_NoDup_fn_args V V_Eqb V_Eqb_ok V V_Eqb V_Eqb_ok V_map V_map_ok V_trie V_trie_ok).
      - exact (model_satisfies_rule_adapter_sort name c args Hin Hsucc).
    Qed.

    (* ============================================================== *)
    (* ===== EQ-RULE ADAPTER (term_eq_rule / sort_eq_rule) ========== *)
    (* ============================================================== *)

    (* ----- Lemma A: assumption-side forward soundness for eq rules -----
       The eq-rule assumption egraph is
         e_assum := rebuild rf (add_open_term false false sub e1 (add_ctx c empty)).
       Mirror of [assumption_egraph_sound] (line 183) but with an
       [add_open_term_sound] step inserted between [add_ctx_sound] and
       [rebuild_sound].  Additionally exposes the root id [x1]'s value:
       the forward witness interpretation [i1] maps [x1] to [inl e1[/sg/]]. *)
    Lemma assumption_egraph_sound_eq c e1 t (sg : subst)
        (Hwfc : wf_ctx l c) (Hwfe1 : wf_term l c e1 t) (Hsg : wf_subst l [] sg c)
      : let sub    := fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)) in
        let e_ctx  := snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)) in
        let x1     := fst (add_open_term succ sort_of l false false sub e1 e_ctx) in
        let e_open := snd (add_open_term succ sort_of l false false sub e1 e_ctx) in
        let e_assum := snd (rebuild rf e_open) in
        egraph_ok e_assum
        /\ exists i1,
             egraph_sound_for_interpretation (lang_model l) i1 e_assum
             /\ map fst sub = map fst c
             /\ args_in_instance l (map snd sg) i1 (map snd sub)
             /\ option_relation (domain_eq V (lang_model l))
                  (map.get i1 x1) (Some (inl e1[/sg/])).
    Proof.
      cbn zeta.
      set (sub    := fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))).
      set (e_ctx  := snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))).
      set (x1     := fst (add_open_term succ sort_of l false false sub e1 e_ctx)).
      set (e_open := snd (add_open_term succ sort_of l false false sub e1 e_ctx)).
      set (e_assum := snd (rebuild rf e_open)).
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
      destruct Hext1 as (Hok_ctx & _ & Hsnd_ctx & _).
      change (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))) with e_ctx in Hok_ctx, Hsnd_ctx.
      change (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))) with sub in Hfst1, Hai1.
      (* Step 3: add_open_term_sound on e1 *)
      pose proof (@Theorems.add_open_term_sound
                    V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok
                    succ sort_of lt lt_asymmetric lt_succ lt_trans
                    X HX l Hwf Hsof false
                    c sub (map snd sg) e1 t
                    (@Theorems.wf_args_from_wf_subst V V_Eqb l [] sg c Hsg)
                    Hwfe1 Hwfc
                    (eq_sym Hfst1) i1)
        as Hvc_open.
      unfold vc in Hvc_open.
      specialize (Hvc_open e_ctx).
      unfold Theorems.open_term_post in Hvc_open.
      specialize (Hvc_open Hok_ctx Hsnd_ctx Hai1).
      destruct Hvc_open as [i2 (Hext_open & Hroot)].
      change (snd (add_open_term succ sort_of l false false sub e1 e_ctx)) with e_open in Hext_open.
      change (fst (add_open_term succ sort_of l false false sub e1 e_ctx)) with x1 in Hroot.
      destruct Hext_open as (Hok_open & Hext12 & Hsnd_open & _).
      (* Rewrite with_names_from c (map snd sg) = sg *)
      assert (Heq_wn : with_names_from c (map snd sg) = sg).
      { pose proof (wf_subst_dom_eq Hsg) as Hdom.
        revert Hdom. clear -sg c. revert sg.
        induction c as [|[n0 t0] c_rest IH]; destruct sg as [|[n1 e1] sg_rest];
          cbn; intros Hdom; auto; try discriminate.
        inversion Hdom; subst. f_equal. apply IH. exact H1. }
      rewrite Heq_wn in Hroot.
      (* Step 4: rebuild_sound on e_open *)
      pose proof (@Semantics.rebuild_sound
                    V V_Eqb V_Eqb_ok lt succ V_default V V_Eqb V_Eqb_ok
                    V_map V_map_ok V_map V_map_ok
                    V_trie V_trie_ok unit HX
                    (lang_model l)
                    (@Theorems.lang_model_ok V V_Eqb V_Eqb_ok sort_of l Hsof Hwf)
                    (fun _ => True) rf)
        as Hvc_rb.
      unfold vc in Hvc_rb.
      specialize (Hvc_rb e_open).
      cbn [snd] in Hvc_rb.
      specialize (Hvc_rb Hok_open).
      destruct Hvc_rb as [Hok_assum Hde_assum].
      pose proof (proj1 (Hde_assum i2) Hsnd_open) as Hsnd_assum.
      fold e_assum in Hok_assum, Hsnd_assum.
      (* Step 5: assemble *)
      split; [exact Hok_assum|].
      exists i2. split; [exact Hsnd_assum|].
      split; [exact Hfst1|].
      split.
      - exact (@Theorems.args_in_instance_monotone
                 V V_Eqb V_map sort_of l (map snd sg) i1 i2
                 (map snd sub) Hext12 Hai1).
      - exact Hroot.
    Qed.

    (* ===== conclusion forward chain: given wf_subst for a term_eq_rule,
       produce a sound interpretation for the conclusion egraph
       (after add_open_term e2 + union x1 x2 + rebuild + force_equiv). ===== *)
    Lemma conclusion_egraph_sound_eq name c e1 e2 t (sg : subst)
        (Hin : In (name, term_eq_rule c e1 e2 t) l)
        (Hsg : wf_subst l [] sg c)
      : let sub     := fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)) in
        let e_ctx   := snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)) in
        let x1      := fst (add_open_term succ sort_of l false false sub e1 e_ctx) in
        let e_open1 := snd (add_open_term succ sort_of l false false sub e1 e_ctx) in
        let e_assum := snd (rebuild rf e_open1) in
        let x2      := fst (add_open_term succ sort_of l true false sub e2 e_assum) in
        let e_open2 := snd (add_open_term succ sort_of l true false sub e2 e_assum) in
        let e_union := snd (@Defs.union V V_Eqb V V_map V_map V_trie unit HX x1 x2 e_open2) in
        let e_concl := snd (force_equiv V V_Eqb V V_map V_map V_trie (X:=unit) (snd (rebuild rf e_union))) in
        exists i2,
          egraph_sound_for_interpretation (lang_model l) i2 e_concl
          /\ args_in_instance l (map snd sg) i2 (map snd sub)
          /\ (exists i1, egraph_sound_for_interpretation (lang_model l) i1 e_assum /\ map.extends i2 i1).
    Proof.
      cbn zeta.
      set (sub    := fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))).
      set (e_ctx  := snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))).
      set (x1     := fst (add_open_term succ sort_of l false false sub e1 e_ctx)).
      set (e_open1 := snd (add_open_term succ sort_of l false false sub e1 e_ctx)).
      set (e_assum := snd (rebuild rf e_open1)).
      set (x2     := fst (add_open_term succ sort_of l true false sub e2 e_assum)).
      set (e_open2 := snd (add_open_term succ sort_of l true false sub e2 e_assum)).
      set (e_union := snd (@Defs.union V V_Eqb V V_map V_map V_trie unit HX x1 x2 e_open2)).
      (* Step 1: wf facts from rule membership *)
      pose proof (rule_in_wf _ _ Hwf Hin) as Hr.
      rewrite app_nil_r in Hr. rewrite invert_wf_term_eq_rule in Hr.
      destruct Hr as (Hwfc & Hwfe1 & Hwfe2 & _).
      (* Step 2: use assumption_egraph_sound_eq for the base *)
      pose proof (assumption_egraph_sound_eq c e1 t sg Hwfc Hwfe1 Hsg)
        as (Hok_assum & i1 & Hsnd_assum & Hfst_sub & Hai1 & Hroot1).
      fold e_ctx sub x1 e_open1 e_assum in Hok_assum, Hsnd_assum, Hfst_sub, Hai1, Hroot1.
      (* with_names_from c (map snd sg) = sg *)
      assert (Heq_wn : with_names_from c (map snd sg) = sg).
      { pose proof (wf_subst_dom_eq Hsg) as Hdom. revert Hdom. clear -sg c. revert sg.
        induction c as [|[n0 t0] c_rest IH]; destruct sg as [|[n1 e0] sg_rest];
          cbn; intros Hdom; auto; try discriminate.
        inversion Hdom; subst. f_equal. apply IH. exact H1. }
      (* Step 3: add_open_term_sound on e2 starting from e_assum, i1 *)
      pose proof (@Theorems.add_open_term_sound
                    V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok
                    succ sort_of lt lt_asymmetric lt_succ lt_trans
                    X HX l Hwf Hsof true
                    c sub (map snd sg) e2 t
                    (@Theorems.wf_args_from_wf_subst V V_Eqb l [] sg c Hsg)
                    Hwfe2 Hwfc (eq_sym Hfst_sub) i1)
        as Hvc_open2.
      unfold vc in Hvc_open2. specialize (Hvc_open2 e_assum).
      unfold Theorems.open_term_post in Hvc_open2.
      specialize (Hvc_open2 Hok_assum Hsnd_assum Hai1).
      destruct Hvc_open2 as [i2a (Hext_open2 & Hroot2)].
      fold e_open2 x2 in Hext_open2, Hroot2.
      destruct Hext_open2 as (Hok_open2 & Hext_1_2a & Hsnd_open2 & Hkey_mono_1_2a).
      rewrite Heq_wn in Hroot2.
      (* Step 4: has_key x2 in e_open2 *)
      assert (Hkey_x2 : Sep.has_key x2 (parent (equiv e_open2))).
      { apply (Semantics.interpretation_exact V V V_map V_map V_trie unit
                 (lang_model l) i2a e_open2 Hsnd_open2 x2).
        unfold Is_Some, option_relation in *.
        destruct (map.get i2a x2); [exact I | discriminate Hroot2]. }
      (* Step 5: has_key x1 in e_open2 via e_assum + key monotonicity *)
      assert (Hkey_x1 : Sep.has_key x1 (parent (equiv e_open2))).
      { apply Hkey_mono_1_2a.
        apply (Semantics.interpretation_exact V V V_map V_map V_trie unit
                 (lang_model l) i1 e_assum Hsnd_assum x1).
        unfold Is_Some, option_relation in *.
        destruct (map.get i1 x1); [exact I | discriminate Hroot1]. }
      (* Step 6: eq_sound_for_model i2a x1 x2 via term_eq_concl *)
      assert (Heq_xy : Semantics.eq_sound_for_model V V V_map (lang_model l) i2a x1 x2).
      { unfold Semantics.eq_sound_for_model, Is_Some_satisfying, option_relation in *.
        destruct (map.get i1 x1) as [v1|] eqn:Hg1; [|discriminate Hroot1].
        pose proof (Properties.map.extends_get Hg1 Hext_1_2a) as Hg1'.
        rewrite Hg1'.
        destruct (map.get i2a x2) as [v2|] eqn:Hg2; [|discriminate Hroot2].
        cbn [Is_Some_satisfying].
        pose proof (@Theorems.lang_model_ok V V_Eqb V_Eqb_ok sort_of l Hsof Hwf) as Hlm_ok.
        pose proof (@ConclSemantic.term_eq_concl V V_Eqb l Hwf name c e1 e2 t Hin sg Hsg)
          as Heq_e1e2.
        exact (let Hle12 := @Theorems.lm_eq_terms V V_Eqb l e1[/sg/] e2[/sg/] t[/sg/] Heq_e1e2 in
               @PER_Transitive _ _ (domain_eq_PER V (model_ok:=Hlm_ok)) _ _ _
                (@PER_Transitive _ _ (domain_eq_PER V (model_ok:=Hlm_ok)) _ _ _ Hroot1 Hle12)
                (@PER_Symmetric _ _ (domain_eq_PER V (model_ok:=Hlm_ok)) _ _ Hroot2)). }
      (* Step 7: union step — preserves soundness and ok *)
      pose proof (@QueryOptSound.union_preserves_egraph_sound_for_interpretation
                    V V_Eqb V_Eqb_ok lt succ V_default V V_map V_map V_map_ok V_trie
                    (lang_model l)
                    (@Theorems.lang_model_ok V V_Eqb V_Eqb_ok sort_of l Hsof Hwf)
                    x1 x2 i2a)
        as Hvc_union.
      unfold vc in Hvc_union.
      specialize (Hvc_union e_open2 Hok_open2 Hsnd_open2 Hkey_x1 Hkey_x2 Heq_xy).
      fold e_union in Hvc_union.
      pose proof (@QueryOptSound.union_preserves_egraph_ok
                    V V_Eqb V_Eqb_ok lt succ V_default V V_map V_map V_map_ok V_trie
                    x1 x2)
        as Hvc_union_ok.
      unfold vc in Hvc_union_ok.
      specialize (Hvc_union_ok e_open2 Hok_open2 Hkey_x1 Hkey_x2).
      fold e_union in Hvc_union_ok.
      (* Step 8: rebuild_sound on e_union *)
      pose proof (@Semantics.rebuild_sound
                    V V_Eqb V_Eqb_ok lt succ V_default V V_Eqb V_Eqb_ok
                    V_map V_map_ok V_map V_map_ok
                    V_trie V_trie_ok unit HX
                    (lang_model l)
                    (@Theorems.lang_model_ok V V_Eqb V_Eqb_ok sort_of l Hsof Hwf)
                    (fun _ => True) rf)
        as Hvc_rb.
      unfold vc in Hvc_rb. specialize (Hvc_rb e_union). cbn [snd] in Hvc_rb.
      specialize (Hvc_rb Hvc_union_ok).
      destruct Hvc_rb as [Hok_rb Hde_rb].
      pose proof (proj1 (Hde_rb i2a) Hvc_union) as Hsnd_rb.
      set (e_rb := snd (rebuild rf e_union)).
      (* Step 9: force_equiv_preserves_sound *)
      pose proof (@QueryOptSound.force_equiv_preserves_sound
                    V V_Eqb V_Eqb_ok lt V V_map V_map V_map_ok V_trie
                    (lang_model l) i2a e_rb
                    (Semantics.egraph_equiv_ok V lt V V_map V_map V_trie unit e_rb Hok_rb)
                    Hsnd_rb)
        as Hsnd_concl.
      (* Step 10: assemble *)
      exists i2a.
      split.
      - exact Hsnd_concl.
      - split.
        + exact (@Theorems.args_in_instance_monotone
                    V V_Eqb V_map sort_of l (map snd sg) i1 i2a
                    (map snd sub) Hext_1_2a Hai1).
        + exact (ex_intro _ i1 (conj Hsnd_assum Hext_1_2a)).
    Qed.

  End Adapter.
End WithVar.
