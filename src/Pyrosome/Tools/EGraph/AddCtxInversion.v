(* ============================================================== *)
(* Source-rule adapter — assumption-inversion layer.              *)
(*                                                                *)
(* Carved out of Theorems.v (the F1cDischarge section + the post- *)
(* WithVar [E]-establishment block) to keep that file smaller and *)
(* to give the forthcoming (B0) source-rule soundness adapter     *)
(* [model_satisfies_rule (lang_model l) (rule_to_log_rule ...)]   *)
(* its own home, built right on top of [add_ctx_inversion].       *)
(*                                                                *)
(* This file Requires Theorems and re-exposes the section-closed  *)
(* constants the moved proofs reference (companion-section style,  *)
(* matching the Semantics.v split).  No proof bodies change.      *)
(* ============================================================== *)
From Stdlib Require Import Lists.List Classes.RelationClasses BinNums.
Import ListNotations.
Open Scope list.


From coqutil Require Import Map.Interface Datatypes.Result.

From Utils Require Import Utils UnionFind Monad ExtraMaps VC Relations Result.
From Utils.EGraph Require Import Defs Semantics QueryOpt SemanticsParents SemanticsAreUnified SemanticsSaturate SemanticsUnionSem SemanticsLSurvive SemanticsRebuildCanon SemanticsAnalysesCover SemanticsHashDb.
Import Monad.StateMonad.
From Pyrosome.Theory Require Import Core ModelImpls.
From Pyrosome.Theory Require WfCutElim.
Import Core.Notations.
From Pyrosome.Tools.EGraph Require Import Defs.
From Pyrosome.Tools.EGraph Require Import Theorems.


#[local] Hint Resolve Properties.map.extends_refl : utils.
#[local] Hint Rewrite combine_map_fst_snd : utils.


Section WithVar.
  Context (V : Type)
    {V_Eqb : Eqb V}
    {V_Eqb_ok : Eqb_ok V_Eqb}
    {V_default : WithDefault V}.

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).

  Notation eq_subst l :=
    (eq_subst (Model:= core_model l)).
  Notation eq_args l :=
    (eq_args (Model:= core_model l)).
  Notation wf_subst l :=
    (wf_subst (Model:= core_model l)).
  Notation wf_args l :=
    (wf_args (Model:= core_model l)).
  Notation wf_ctx l :=
    (wf_ctx (Model:= core_model l)).


  Context
    (V_map : forall A, map.map V A)
      (V_map_plus : ExtraMaps.map_plus V_map)
      (V_map_ok : forall A, map.ok (V_map A))
      (V_trie : forall A, map.map (list V) A)
      (V_trie_ok : forall A, map.ok (V_trie A)).

  Notation instance := (instance V V V_map V_map V_trie).

  Notation atom := (atom V V).


  Context (succ : V -> V).

  (* Include sort_of as special symbol/fn in db. *)
  Context (sort_of : V).

  Context (lt : V -> V -> Prop).

  Context (lt_asymmetric : Asymmetric lt)
    (lt_succ : forall x, lt x (succ x))
    (lt_trans : Transitive lt).

  (* --- re-exposed Theorems section-closed constants, applied to the
     ambient WithVar context, so the F1cDischarge body below compiles
     verbatim (add_ctx_egraph_ok / add_ctx_readback have an implicit
     analysis arg, so their two call sites are written in explicit
     @Theorems.* form instead of via a notation). --- *)
  Local Notation lang_model := (@Theorems.lang_model V V_Eqb sort_of).
  Local Notation lang_model_ok := (@Theorems.lang_model_ok V V_Eqb V_Eqb_ok sort_of).
  Local Notation is_root := (@Theorems.is_root V V_map V_trie).
  Local Notation db_ctx_inv := (@Theorems.db_ctx_inv V V_map V_trie sort_of).
  Local Notation ctx_readback_to_eF := (@Theorems.ctx_readback_to_eF V V_Eqb V_default V_map V_trie sort_of).
  Local Notation ctx_readback_wf_subst := (@Theorems.ctx_readback_wf_subst V V_Eqb V_Eqb_ok V_default V_map V_trie sort_of).

  Section F1cDischarge.
    Context (X : Type) `{HX : analysis V V X}.
    Context (l : lang) (Hwf : wf_lang l) (Hsof : fresh sort_of l).
    Context (V_map_plus_ok : ExtraMaps.map_plus_ok V_map).
    Context (V_trie_plus : ExtraMaps.map_plus V_trie).
    Context (sli : forall B, WithDefault B -> (B -> B -> B) ->
                   ne_list (V_trie B * list bool) -> V_trie B).

    Local Notation lang_model := (lang_model l).
    Local Notation egraph_ok := (egraph_ok V lt V V_map V_map V_trie X).
    Local Notation ain a e := (@Semantics.atom_in_egraph V V V_map V_map V_trie X a e).
    Local Notation interp := (V_map (lang_model.(domain _))).
    Local Notation asnd a al := (@Semantics.atom_sound_for_model V V V_map lang_model a al).

    (* [W] rewiring: the canonicalizing survival, now derived from the
       0-axiom rebuild kernel [rebuild_canon] + [L_survive_canonical']
       instead of the [Admitted] axiom [L_survive_canonical].  The [n = 0]
       case is excluded by the [Success] (drained) hypothesis (rebuild 0 =
       Failure); the [n = S fuel] case applies [rebuild_canon] (db_inv(True)
       eF + roots_mono e1 eF) then [L_survive_canonical']. *)
    Lemma rebuild_survives_canonical (e1 : instance X) (n : nat)
      (Hok : egraph_ok e1)
      (Hgwl : exists ed_list, good_worklist V V V_map V_map V_trie X e1 ed_list)
      (Hsucc : fst (rebuild n e1) = Result.Success tt)
      : forall a : atom,
          atom_in_egraph_up_to_equiv V V V_map V_map V_trie X a e1 ->
          all (is_root X e1) (atom_args a) ->
          is_root X e1 (atom_ret a) ->
          ain a (snd (rebuild n e1)).
    Proof.
      intros a Hup Hargs Hret.
      destruct n as [|fuel].
      - (* rebuild 0 = Mret (Failure ...), contradicts the Success gate *)
        exfalso. cbn in Hsucc. discriminate Hsucc.
      - destruct Hgwl as [ed_list Hgwl].
        pose proof (@rebuild_canon V V_Eqb V_Eqb_ok lt succ V_default
                      V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                      X _ lang_model (lang_model_ok l Hsof Hwf)
                      fuel e1 ed_list Hok Hgwl) as [HdbT Hmono].
        eapply (@L_survive_canonical' V V_Eqb V_Eqb_ok lt succ V_default
                      V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                      X _ lang_model (lang_model_ok l Hsof Hwf)
                      (S fuel) e1 a).
        + exact Hok.
        + exact Hup.
        + exact HdbT.
        + eapply all_wkn; [ intros x _ Hx; exact (Hmono x Hx) | exact Hargs ].
        + exact (Hmono (atom_ret a) Hret).
    Qed.

    (* ============================================================ *)
    (* Assembly: from an adversary [a] sound on the rebuilt           *)
    (* assumption egraph's atoms, recover a wf substitution of [c].   *)
    (* Linearly chains add_ctx_egraph_ok + add_ctx_readback +         *)
    (* db_inv_db_injective + rebuild_survives_canonical +             *)
    (* ctx_readback_to_eF + ctx_readback_wf_subst.                    *)
    Lemma add_ctx_inversion (rf : nat) (a : interp) c
      : wf_ctx l c ->
        (* [E] obligation: the good_worklist witness for the add_ctx output,
           discharged 0-axiom by [add_ctx_good_worklist] (proved after
           [End WithVar], since its proof needs the fully-closed signatures
           of the [add_open_sort] lemmas). *)
        (exists ed_list, good_worklist V V V_map V_map V_trie X
           (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
           ed_list) ->
        fst (rebuild rf (snd (add_ctx succ sort_of l false false c
                                (empty_egraph V_default X)))) = Result.Success tt ->
        (forall al, ain al (snd (rebuild rf (snd (add_ctx succ sort_of l false false c
                                                   (empty_egraph V_default X)))))
                  -> asnd a al) ->
        exists sg, wf_subst l [] sg c
                /\ map fst sg = map fst c
                /\ (forall x, In x (map fst (fst (add_ctx succ sort_of l false false c
                                                  (empty_egraph V_default X)))) ->
                      map.get a (named_list_lookup default
                                  (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))) x)
                        = Some (inl (named_list_lookup default sg x))).
    Proof.
      intros Hwfc Hgwl Hsucc Hsound.
      change (empty_egraph V_default X)
        with (@empty_egraph V V_default V V_map V_map V_trie X) in *.
      set (e0 := @empty_egraph V V_default V V_map V_map V_trie X) in *.
      set (sub := fst (add_ctx succ sort_of l false false c e0)) in *.
      set (e1 := snd (add_ctx succ sort_of l false false c e0)) in *.
      set (eF := snd (rebuild rf e1)) in *.
      (* --- base facts at empty_egraph --- *)
      assert (Hok0 : egraph_ok e0).
      { exact (proj1 (@empty_sound_for_interpretation V lt succ V_default V V_map V_map_ok
                        V_map V_map_ok V_trie X lang_model)). }
      assert (Huf0 : exists roots, union_find_ok lt (Defs.equiv e0) roots).
      { exact (ex_intro _ [] (@union_find_empty_ok V lt succ V_default V_map V_map_ok)). }
      assert (Hdb0 : db_ctx_inv X e0).
      { intros aa Hin. exfalso.
        unfold Semantics.atom_in_db in Hin.
        unfold e0 in Hin. cbn [Defs.db empty_egraph] in Hin.
        rewrite map.get_empty in Hin.
        exact Hin. }
      (* --- add_ctx_egraph_ok: structural envelope --- *)
      pose proof (@Theorems.add_ctx_egraph_ok V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as HE.
      unfold vc in HE. specialize (HE e0).
      fold sub e1 in HE.
      specialize (HE Huf0 Hdb0 Hok0).
      destruct HE as (Huf1 & Hdb1 & Hroots1 & Hmapfst & Hok1).
      (* --- add_ctx_readback: model-free per-var readback --- *)
      pose proof (@Theorems.add_ctx_readback V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as HR.
      unfold vc in HR. specialize (HR e0).
      fold sub e1 in HR.
      specialize (HR Huf0 Hdb0).
      destruct HR as (_ & _ & _ & _ & Hrb).
      (* --- canonicalizing survival for eF (0-axiom rebuild kernel),
             using the supplied good_worklist witness [Hgwl] (folded to e1) --- *)
      pose proof (rebuild_survives_canonical e1 rf Hok1 Hgwl Hsucc) as Hsurv.
      (* --- ctx_readback (e1) -> ctx_readback_eF (eF) --- *)
      pose proof (ctx_readback_to_eF X l Hsof e1 eF Hdb1 Hsurv c sub Hwfc Hroots1 Hrb) as Hrbef.
      (* --- finish: build wf_subst from eF readback + a sound on eF --- *)
      pose proof (ctx_readback_wf_subst X l Hwf Hsof eF a Hsound c sub Hwfc
                    (eq_sym Hmapfst) Hrbef) as Hfin.
      exact Hfin.
    Qed.

  End F1cDischarge.
End WithVar.

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
  Notation lang := (@lang V).

  Notation wf_subst l :=
    (wf_subst (Model:= core_model l)).
  Notation wf_ctx l :=
    (wf_ctx (Model:= core_model l)).

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

  Section AddCtxInvert.
    Context (X : Type) `{HX : analysis V V X}.
    Context (l : lang) (Hwf : wf_lang l) (Hsof : fresh sort_of l).

    Local Notation lang_model := (lang_model V sort_of l).
    Local Notation interp := (V_map (lang_model.(domain _))).

    Set Printing Width 120.

    (* The combined postcondition (inlined for scratch interactive dev;
       in Theorems.v this becomes a Definition ctx_good_worklist_post):
       ctx_egraph_post's 5 structural conjuncts, plus the two threaded
       invariants (parents_keys_in_equiv, analyses_cover), plus the
       existential good_worklist witness. *)
    Lemma add_ctx_good_worklist_vc c
      : wf_ctx l c ->
        vc (add_ctx succ sort_of l false false c)
          (fun e_in res =>
      (exists roots, union_find_ok lt (Defs.equiv e_in) roots) ->
      @db_inv V V V_map V_map V_trie X (fun _ => True) e_in ->
      egraph_ok V lt V V_map V_map V_trie X e_in ->
      parents_keys_in_equiv V V V_map V_map V_trie X e_in ->
      SemanticsAnalysesCover.analyses_cover V V V_map V_map V_trie X e_in ->
      Defs.worklist e_in = [] ->
      (exists roots, union_find_ok lt (Defs.equiv (snd res)) roots)
      /\ db_ctx_inv V V_map V_trie sort_of X (snd res)
      /\ all (fun p => is_root V V_map V_trie X (snd res) (snd p)) (fst res)
      /\ map fst (fst res) = map fst c
      /\ egraph_ok V lt V V_map V_map V_trie X (snd res)
      /\ parents_keys_in_equiv V V V_map V_map V_trie X (snd res)
      /\ SemanticsAnalysesCover.analyses_cover V V V_map V_map V_trie X (snd res)
      /\ (exists ed_list, good_worklist V V V_map V_map V_trie X (snd res) ed_list)).
    Proof.
      intros Hctx. unfold add_ctx. induction c as [|[name t] c' IH].
      - (* nil case: e_in is the fixed original (empty_egraph at the caller);
           db_inv(True) gives every atom a root ret, so coverage is vacuous
           and good_worklist holds with ed_list = []. *)
        cbn [list_Mfoldr]. unfold vc, Mret. cbn [StateMonad.state_monad].
        intros e_in Hok Hdb Hok_eg Hpke Hac Hwl.
        cbn [fst snd].
        assert (Hdbctx : db_ctx_inv V V_map V_trie sort_of X e_in).
        { unfold db_ctx_inv, db_inv. intros a Ha. destruct (Hdb a Ha) as [Hargs Hret].
          split; [exact Hargs | intros _; apply Hret; exact I]. }
        split; [exact Hok|].
        split; [exact Hdbctx|].
        split; [cbn; exact I|].
        split; [cbn; reflexivity|].
        split; [exact Hok_eg|].
        split; [exact Hpke|].
        split; [exact Hac|].
        exists nil.
        unfold good_worklist.
        split; [ rewrite Hwl; reflexivity |].
        split; [ constructor |].
        split; [ exact I |].
        split; [ intros dj dk Hj Hk Hne; cbn in Hj; contradiction |].
        split.
        { intros a Ha. destruct (Hdb a Ha) as [Hargs _].
          split; [exact Hargs | intros HF; destruct HF]. }
        intros b Hb Hnr. exfalso. apply Hnr.
        destruct (Hdb b Hb) as [_ Hret]. apply Hret. exact I.
      - (* cons case: the E3 assembly.  Per-op threading (add_open_sort/alloc/
           hash/union) of the 5 ctx_egraph_post conjuncts + parents_keys_in_equiv
           + analyses_cover + equiv_extends.  All VERIFIED (state 4855); only the
           good_worklist existential (conjunct 8) remains [admit].  Uses
           add_open_sort_node_atoms (equiv_extends, from add_ctx_readback@5369). *)
        cbn [list_Mfoldr]. eapply vc_bind.
        { apply IH. inversion Hctx; assumption. }
        intros e_pre base'. cbn [Mbind StateMonad.state_monad Mret].
        unfold vc; intros e_inner Htail.
        intros Hok Hdb Hok_eg Hpke Hac Hwl.
        specialize (Htail Hok Hdb Hok_eg Hpke Hac Hwl).
        assert (Hwfc' : wf_ctx l c') by (inversion Hctx; assumption).
        assert (Hwfst : wf_sort l c' t) by (inversion Hctx; assumption).
        destruct Htail as (Huf_tail & Hdb_tail & Hall_tail & Hfst_tail & Hok_eg_tail & Hpke_tail & Hac_tail & Hgwl_tail).
        (* ---- add_open_sort step ---- *)
        assert (Hmaps : map fst c' = map fst base') by (symmetry; exact Hfst_tail).
        assert (Hbase_keys : all (fun p => Sep.has_key (snd p) (parent (Defs.equiv e_inner))) base').
        { eapply all_wkn; [|exact Hall_tail]. intros p _ Hp_root. apply is_root_has_key. exact Hp_root. }
        pose proof (@add_open_sort_node_atoms V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c' base' t Hwfc' Hwfst Hmaps) as Hnode.
        pose proof (@add_open_sort_egraph_ok V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf c' base' t Hwfc' Hwfst Hmaps) as Hsort_eg.
        pose proof (@add_open_sort_parents_keys_in_equiv V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf c' base' t Hwfc' Hwfst Hmaps) as Hsort_pke.
        pose proof (@add_open_sort_worklist_frame V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf c' base' t Hwfc' Hwfst Hmaps) as Hsort_wl.
        unfold vc in Hnode, Hsort_eg, Hsort_pke, Hsort_wl.
        specialize (Hnode e_inner). specialize (Hsort_eg e_inner). specialize (Hsort_pke e_inner). specialize (Hsort_wl e_inner).
        unfold open_atomtree_sort_post, open_egraph_sort_post, open_egraph_post, open_pke_sort_post, open_pke_post, open_wlframe_sort_post, open_wlframe_post in *.
        destruct (add_open_sort succ sort_of l false false base' t e_inner) as [t_v e_sort] eqn:Heq_sort.
        cbn [fst snd] in Hnode, Hsort_eg, Hsort_pke, Hsort_wl.
        specialize (Hnode Huf_tail Hdb_tail Hall_tail).
        destruct Hnode as (Henv_sort & Htv_root & Htree_sort & Hext_sort).
        destruct Henv_sort as (Huf_sort & Hdb_sort & Hincl_sort & Hmono_sort).
        specialize (Hsort_eg Hok_eg_tail Hbase_keys).
        destruct Hsort_eg as (Hok_eg_sort & Hmono_eg_sort & Htv_key_sort).
        specialize (Hsort_pke Hok_eg_tail Hpke_tail Hbase_keys).
        destruct Hsort_pke as (_ & Hpke_sort & _ & _).
        specialize (Hsort_wl Hok_eg_tail Hac_tail Hbase_keys).
        destruct Hsort_wl as (Hwl_sort & _ & Hac_sort & _ & _).
        (* ---- alloc_opaque step ---- *)
        pose proof (@alloc_opaque_rank_zero V V_Eqb V_Eqb_ok lt succ V V_map V_map V_map_ok V_trie X HX lt_asymmetric lt_succ lt_trans) as Halloc.
        pose proof (@alloc_opaque_egraph_ok V V_Eqb V_Eqb_ok lt succ V V_map V_map V_map_ok V_trie X HX lt_asymmetric lt_succ lt_trans) as Halloc_eg.
        pose proof (@alloc_opaque_parents_keys_in_equiv V V_Eqb V_Eqb_ok lt succ V V_map V_map V_map_ok V_trie X HX lt_asymmetric lt_succ lt_trans) as Halloc_pke.
        pose proof (@alloc_opaque_analyses_cover V V_Eqb V_Eqb_ok lt succ V V_map V_map V_map_ok V_trie X HX lt_asymmetric lt_succ lt_trans) as Halloc_ac.
        unfold vc in Halloc, Halloc_eg, Halloc_pke, Halloc_ac.
        specialize (Halloc e_sort). specialize (Halloc_eg e_sort). specialize (Halloc_pke e_sort). specialize (Halloc_ac e_sort).
        destruct (alloc_opaque V succ V V_map V_map V_trie X e_sort) as [x' e_alloc] eqn:Heq_alloc.
        cbn [fst snd] in Halloc, Halloc_eg, Halloc_pke, Halloc_ac.
        destruct Huf_sort as [roots_s Hroots_s].
        specialize (Halloc roots_s Hroots_s).
        destruct Halloc as (Hok_alloc & Hfresh_x' & Hx'_root & Hx'_rank0 & Hkeys_alloc & Hmono_alloc & Hdb_alloc_eq & Hpar_alloc & Hwl_alloc).
        specialize (Halloc_eg Hok_eg_sort).
        destruct Halloc_eg as (Hok_eg_alloc & _ & Hx'_key_alloc & Hmono_eg_alloc & _ & _ & _).
        specialize (Halloc_pke Hok_eg_sort Hpke_sort).
        specialize (Halloc_ac Hok_eg_sort Hac_sort).
        destruct Halloc_ac as (Hac_alloc & Hax'_analysis).
        cbn [fst snd] in *.
        assert (Hdb_alloc : db_ctx_inv V V_map V_trie sort_of X e_alloc) by
          (unfold db_ctx_inv, db_inv in *; intros a Ha; rewrite <- Hdb_alloc_eq in Ha;
           specialize (Hdb_sort a Ha); destruct Hdb_sort as [Hargs_roots Hret_root]; split;
           [ eapply all_wkn; [|exact Hargs_roots]; intros z _ Hz; exact (Hmono_alloc z Hz)
           | intro HPfn; exact (Hmono_alloc _ (Hret_root HPfn)) ]).
        assert (Hext_alloc : equiv_extends V V V_map V_map V_trie X e_sort e_alloc) by
          (pose proof (@alloc_opaque_parent_eq V V_map V_trie succ X HX e_sort) as Hpar_sort;
           cbn [fst snd] in Hpar_sort; rewrite Heq_alloc in Hpar_sort; cbn [fst snd] in Hpar_sort;
           assert (Hnone_x' : map.get (parent (Defs.equiv e_sort)) x' = None) by
             (unfold Sep.has_key in Hfresh_x'; destruct (map.get (parent (Defs.equiv e_sort)) x'); tauto);
           unfold equiv_extends, uf_rel_PER; intros i j Hpre; rewrite Hpar_sort;
           eapply uf_rel_PER_alloc_monotone; [exact V_map_ok | exact Hnone_x' | unfold uf_rel_PER; exact Hpre]).
        (* ---- hash_entry step (structural) ---- *)
        assert (Hno_sortof : forall r, ~ atom_in_db V V V_map V_trie X (Build_atom sort_of [x'] r) e_alloc.(Defs.db)) by
          (intros r Hin; rewrite <- Hdb_alloc_eq in Hin; unfold db_ctx_inv, db_inv in Hdb_sort;
           specialize (Hdb_sort (Build_atom sort_of [x'] r) Hin); destruct Hdb_sort as [Hargs_s _];
           cbn [atom_args] in Hargs_s; destruct Hargs_s as [Hx'_s _];
           assert (Hx'_ks : Sep.has_key x' (parent (Defs.equiv e_sort))) by (apply is_root_has_key; unfold is_root; exact Hx'_s);
           exact (Hfresh_x' Hx'_ks)).
        assert (Hkeys_he_args : forall y, In y [x'] -> Sep.has_key y (parent (Defs.equiv e_alloc))) by
          (intros y Hy; cbn in Hy; destruct Hy as [Hy|]; [|contradiction]; subst y; exact Hx'_key_alloc).
        assert (Hx'_root_list : all (fun y => map.get (parent (Defs.equiv e_alloc)) y = Some y) [x']) by
          (cbn; split; [exact Hx'_root | exact I]).
        pose proof (@hash_entry_all_roots V V_Eqb V_Eqb_ok lt succ V_default V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok X HX (fun s => s <> sort_of) lt_asymmetric lt_succ lt_trans sort_of [x']) as Hhe_roots.
        pose proof (@hash_entry_fresh_rank_zero V V_Eqb V_Eqb_ok lt succ V_default V V_map V_map_ok V_map V_map_ok V_trie V_trie_ok X HX lt_asymmetric lt_succ lt_trans sort_of [x']) as Hhe_fresh.
        pose proof (@hash_entry_egraph_ok V V_Eqb V_Eqb_ok lt succ V_default V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok X HX lt_asymmetric lt_succ lt_trans sort_of [x']) as Hhe_eg.
        pose proof (@hash_entry_args_old_keys V V_Eqb V_Eqb_ok lt succ V_default V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok X HX lt_asymmetric lt_succ lt_trans (fun s => s <> sort_of) sort_of [x']) as Hhe_old.
        unfold vc in Hhe_roots, Hhe_fresh, Hhe_eg, Hhe_old.
        specialize (Hhe_roots e_alloc). specialize (Hhe_fresh e_alloc). specialize (Hhe_eg e_alloc). specialize (Hhe_old e_alloc).
        destruct (hash_entry succ sort_of [x'] e_alloc) as [tx' e_he] eqn:Heq_he.
        cbn [fst snd] in Hhe_roots, Hhe_fresh, Hhe_eg, Hhe_old.
        specialize (Hhe_roots (ex_intro _ _ Hok_alloc) Hdb_alloc Hkeys_he_args).
        destruct Hhe_roots as (Huf_he & Hdb_he & Hincl_he & Hmono_he & _).
        specialize (Hhe_eg Hok_eg_alloc Hkeys_he_args).
        destruct Hhe_eg as (Hok_eg_he & Hmono_eg_he & Htx'_key_he).
        specialize (Hhe_old (ex_intro _ _ Hok_alloc) Hdb_alloc Hkeys_he_args).
        specialize (Hhe_fresh (ex_intro _ _ Hok_alloc) Hx'_root_list Hno_sortof).
        destruct Hhe_fresh as (Htx'_rank0 & Htx'_root & Htx'_fresh & Htx'_atom).
        (* ---- hash_entry step (pke / analyses_cover / good_ed atom / equiv_extends) ---- *)
        assert (Hall_he_args : all (fun y => Sep.has_key y (parent (Defs.equiv e_alloc))) [x']) by (cbn; split; [exact Hx'_key_alloc | exact I]).
        pose proof (@hash_entry_parents_keys_in_equiv V V_Eqb V_Eqb_ok lt succ V_default V V_map V_map V_map_ok V_trie X HX lt_asymmetric lt_succ lt_trans sort_of [x']) as Hhe_pke.
        unfold vc in Hhe_pke. specialize (Hhe_pke e_alloc). rewrite Heq_he in Hhe_pke. cbn [fst snd] in Hhe_pke.
        specialize (Hhe_pke (ex_intro _ _ Hok_alloc) Hall_he_args Halloc_pke).
        pose proof (@hash_entry_wl_frame V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie succ lt lt_asymmetric lt_succ lt_trans X HX sort_of [x'] e_alloc Hok_eg_alloc Hac_alloc Hkeys_he_args) as Hhe_wl.
        rewrite Heq_he in Hhe_wl. cbn [fst snd] in Hhe_wl.
        destruct Hhe_wl as (Hwl_he & Hac_he).
        pose proof (@hash_entry_sortof_fresh_facts V V_Eqb V_Eqb_ok V_map V_map_ok V_trie succ sort_of lt lt_asymmetric lt_succ lt_trans X HX x') as Hhe_sf.
        unfold vc in Hhe_sf. specialize (Hhe_sf e_alloc). rewrite Heq_he in Hhe_sf. cbn [fst snd] in Hhe_sf.
        specialize (Hhe_sf (ex_intro _ _ Hok_alloc) Hx'_root Hno_sortof Hax'_analysis Halloc_pke).
        destruct Hhe_sf as (Hwl_he_sf & Hpar_tx'_he).
        pose proof (@hash_entry_equiv_extends V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie succ lt lt_asymmetric lt_succ lt_trans X HX sort_of [x']) as Hhe_ext.
        unfold vc in Hhe_ext. specialize (Hhe_ext e_alloc). rewrite Heq_he in Hhe_ext. cbn [fst snd] in Hhe_ext.
        specialize (Hhe_ext (ex_intro _ _ Hok_alloc) Hkeys_he_args).
        (* ---- union step ---- *)
        assert (Htv_root_alloc : map.get (parent (Defs.equiv e_alloc)) t_v = Some t_v) by (exact (Hmono_alloc t_v Htv_root)).
        assert (Htv_root_he : map.get (parent (Defs.equiv e_he)) t_v = Some t_v) by (exact (Hmono_he t_v Htv_root_alloc)).
        assert (Htv_ne_tx' : t_v <> tx') by (intro Heq; subst t_v; apply Htx'_fresh; apply is_root_has_key; exact Htv_root_alloc).
        assert (Htv_key_he : Sep.has_key t_v (parent (Defs.equiv e_he))) by (apply is_root_has_key; exact Htv_root_he).
        pose proof (@union_roots_demote_second V V_Eqb V_Eqb_ok lt V_default V V_map V_map V_map_ok V_trie X HX t_v tx') as Hunion.
        unfold vc in Hunion. specialize (Hunion e_he).
        pose proof (@SemanticsUnionSem.union_preserves_egraph_ok_sem V V_Eqb V_Eqb_ok lt succ V_default V V_map V_map V_map_ok V_trie X HX t_v tx' e_he Hok_eg_he Htv_key_he Htx'_key_he) as Hok_eg_u.
        pose proof (@union_parents_keys_in_equiv V V_Eqb V_Eqb_ok lt succ V_default V V_map V_map V_map_ok V_trie X HX t_v tx') as Hu_pke.
        unfold vc in Hu_pke. specialize (Hu_pke e_he).
        pose proof (@union_analyses_cover V V_Eqb V_Eqb_ok lt succ V_default V V_map V_map V_map_ok V_trie X HX t_v tx') as Hu_ac.
        unfold vc in Hu_ac. specialize (Hu_ac e_he).
        pose proof (@union_sound V V_Eqb V_Eqb_ok lt succ V_default V V_map V_map V_map_ok V_trie X HX t_v tx') as Hu_snd.
        unfold vc in Hu_snd. specialize (Hu_snd e_he).
        destruct (Defs.union t_v tx' e_he) as [v_u e_u] eqn:Heq_union.
        cbn [fst snd] in Hunion, Hok_eg_u, Hu_pke, Hu_ac, Hu_snd.
        destruct Huf_he as [roots_he Hroots_he].
        specialize (Hunion roots_he Hroots_he Htv_root_he Htx'_root Htv_ne_tx' Htx'_rank0).
        destruct Hunion as (Hvu_tv & Htv_root_u & Htx'_demoted_u & Hothers_u & Hdb_u & Hpar_u & [improved Hwl_u] & [roots_u Hroots_u]).
        specialize (Hu_pke (ex_intro _ _ Hroots_he) Htv_key_he Htx'_key_he Hhe_pke).
        specialize (Hu_ac (ex_intro _ _ Hroots_he) Htv_key_he Htx'_key_he Hac_he).
        specialize (Hu_snd (ex_intro _ _ Hroots_he) Htv_key_he Htx'_key_he).
        destruct Hu_snd as (_ & _ & Hper_iff & _).
        assert (Hext_u : equiv_extends V V V_map V_map V_trie X e_he e_u) by
          (unfold equiv_extends, uf_rel_PER; intros i j Hpre; apply Hper_iff;
           unfold Relations.union_closure_PER; apply Relations.PER_clo_base; left; exact Hpre).
        (* ---- db_ctx_inv e_u ---- *)
        assert (Htx'_not_arg : forall b, atom_in_db V V V_map V_trie X b (Defs.db e_he) -> ~ In tx' (atom_args b)) by
          (intros b Hb Hin_tx'; destruct (Hhe_old b Hb) as [Hb_args_old _];
           exact (Htx'_fresh (in_all _ _ _ Hb_args_old Hin_tx'))).
        assert (Hdb_u_inv : db_ctx_inv V V_map V_trie sort_of X e_u) by (
          unfold db_ctx_inv, db_inv in Hdb_he |- *; intros a Ha; rewrite <- Hdb_u in Ha;
          specialize (Hdb_he a Ha); destruct Hdb_he as [Hargs_he Hret_he]; split;
          [ eapply all_wkn; [|exact Hargs_he]; intros y Hyin Hy_root; unfold is_root in Hy_root;
            apply Hothers_u; [ intro Heq; subst y; exact (Htx'_not_arg a Ha Hyin) | exact Hy_root ]
          | intro HPfn;
            assert (Hret_root : map.get (parent (Defs.equiv e_he)) (atom_ret a) = Some (atom_ret a)) by (exact (Hret_he HPfn));
            apply Hothers_u;
            [ intro Heq; subst;
              destruct (Hhe_old a Ha) as [_ Ha_old];
              assert (Ha_alloc : atom_in_db V V V_map V_trie X a (Defs.db e_alloc)) by (apply Ha_old; exact HPfn);
              unfold db_ctx_inv, db_inv in Hdb_alloc;
              specialize (Hdb_alloc a Ha_alloc); destruct Hdb_alloc as [_ Hret_alloc];
              assert (Htx'_hk : Sep.has_key (atom_ret a) (parent (Defs.equiv e_alloc))) by (unfold Sep.has_key; rewrite (Hret_alloc HPfn); exact I);
              exact (Htx'_fresh Htx'_hk)
            | exact Hret_root ] ]).
        (* ---- final assembly: 7 structural conjuncts proven; good_worklist remains ---- *)
        cbn [fst snd].
        split; [exact (ex_intro _ roots_u Hroots_u)|].
        split; [exact Hdb_u_inv|].
        split.
        { cbn [all]. split.
          - unfold is_root. apply Hothers_u.
            + intro Heq. apply Htx'_fresh. rewrite <- Heq. exact Hx'_key_alloc.
            + exact (Hmono_he x' Hx'_root).
          - eapply all_wkn; [|exact Hall_tail]. intros [xn yn] Hyin Hyn_root.
            cbn [snd] in *. unfold is_root in *.
            apply Hothers_u.
            + intro Heq. subst yn. apply Htx'_fresh. apply is_root_has_key. unfold is_root.
              exact (Hmono_alloc _ (Hmono_sort _ Hyn_root)).
            + exact (Hmono_he _ (Hmono_alloc _ (Hmono_sort _ Hyn_root))). }
        split; [cbn [map fst]; f_equal; exact Hfst_tail|].
        split; [exact Hok_eg_u|].
        split; [exact Hu_pke|].
        split; [exact Hu_ac|].
        (* good_worklist e_u (d_head :: ed_list_tail), d_head = {tx';t_v;improved;sort_of[x']->tx'}.
           Facts ready: Hgwl_tail (ed_list_tail), Hpar_tx'_he+Hpar_u (parents[tx']=singleton),
           Htx'_atom+Hdb_u (atom in db), Htv_root_u/Htx'_demoted_u/Hper_iff (good_ed d_head),
           Hwl_u/Hwl_he/Hwl_alloc/Hwl_sort (worklist chain), Hext_*/Hmono_* (E2 tail frame). *)
        destruct Hgwl_tail as [ed_tail Hgood_tail].
        unfold good_worklist in Hgood_tail.
        destruct Hgood_tail as (Hwl_tail_eq & Hnodup_tail & Hall_good_tail & Hdisj_tail & Hdbfalse_tail & Hcov_tail).
        assert (Hx'_ne_tx' : x' <> tx') by (intro Heq; subst x'; exact (Htx'_fresh Hx'_key_alloc)).
        assert (Hx'_notin_inner : ~ Sep.has_key x' (parent (equiv e_inner))) by (intro Hk; exact (Hfresh_x' (Hmono_eg_sort _ Hk))).
        assert (Htx'_notin_inner : ~ Sep.has_key tx' (parent (equiv e_inner))) by (intro Hk; exact (Htx'_fresh (Hkeys_alloc _ (Hmono_eg_sort _ Hk)))).
        assert (Hkey_ne_tx' : forall z, map.get (parent (equiv e_inner)) z = Some z -> z <> tx') by (intros z Hz Heq; subst z; apply Htx'_notin_inner; apply (is_root_has_key V V_map V_trie X e_inner tx'); exact Hz).
        assert (Hlift_root_u : forall z, z <> tx' -> map.get (parent (equiv e_inner)) z = Some z -> map.get (parent (equiv e_u)) z = Some z) by (intros z Hz Hr; apply Hothers_u; [exact Hz | apply Hmono_he; apply Hmono_alloc; exact (Hmono_sort z Hr)]).
        assert (Hlift_db_u : forall a, atom_in_db V V V_map V_trie X a (db e_inner) -> atom_in_db V V V_map V_trie X a (db e_u)) by (intros a Ha; rewrite <- Hdb_u; apply Hincl_he; rewrite <- Hdb_alloc_eq; exact (Hincl_sort a Ha)).
        assert (Hlift_uf_u : forall a b, uf_rel_PER V (V_map V) (V_map nat) (equiv e_inner) a b -> uf_rel_PER V (V_map V) (V_map nat) (equiv e_u) a b) by (intros a b Hab; apply Hext_u; apply Hhe_ext; apply Hext_alloc; apply Hext_sort; exact Hab).
        pose proof (@add_open_sort_parents_frame V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c' base' t Hwfc' Hwfst Hmaps) as HE0.
        unfold vc in HE0. specialize (HE0 e_inner). rewrite Heq_sort in HE0.
        unfold open_parents_frame_sort_post, open_parents_frame_post in HE0. cbn [fst snd] in HE0.
        specialize (HE0 Hok_eg_tail Huf_tail Hdb_tail Hall_tail).
        pose proof (@hash_entry_parents_frame V V_Eqb V_Eqb_ok lt succ V_default V V_map V_map V_map_ok V_trie X HX lt_asymmetric lt_succ lt_trans sort_of [x']) as HE1.
        unfold vc in HE1. specialize (HE1 e_alloc). rewrite Heq_he in HE1. cbn [fst snd] in HE1.
        specialize (HE1 (ex_intro _ _ Hok_alloc) Hkeys_he_args).
        pose proof (@hash_entry_db_reverse V V_Eqb V_Eqb_ok lt succ V_default V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok X HX lt_asymmetric lt_succ lt_trans sort_of [x']) as HR.
        unfold vc in HR. specialize (HR e_alloc). rewrite Heq_he in HR. cbn [fst snd] in HR.
        specialize (HR (ex_intro _ _ Hok_alloc) Hx'_root_list).
        pose proof (@add_open_sort_no_new_sortof V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie succ sort_of lt X HX l Hsof base' t e_inner) as HN.
        rewrite Heq_sort in HN. cbn [snd] in HN.
        assert (Htail_frame : forall d, In d ed_tail -> good_ed V V V_map V_map V_trie X e_u d) by
          (intros d Hd_in;
           pose proof (in_all _ _ _ Hall_good_tail Hd_in) as Hd;
           unfold good_ed in Hd;
           destruct Hd as (Hpar_d & Hatom_d & Hargs_d & Hret_d & Hnew_d & Hne_d & Huf_d);
           assert (Hhk_old_inner : Sep.has_key (ed_old V V d) (parent (equiv e_inner))) by (apply Hpke_tail; exists [ed_atom V V d]; exact Hpar_d);
           assert (Hnew_sort : map.get (parent (equiv e_sort)) (ed_new V V d) = Some (ed_new V V d)) by (apply Hmono_sort; exact Hnew_d);
           assert (Hnew_he : map.get (parent (equiv e_he)) (ed_new V V d) = Some (ed_new V V d)) by (apply Hmono_he; apply Hmono_alloc; exact Hnew_sort);
           assert (Huf_sort : uf_rel_PER V (V_map V) (V_map nat) (equiv e_sort) (ed_old V V d) (ed_new V V d)) by (apply Hext_sort; exact Huf_d);
           assert (Huf_he : uf_rel_PER V (V_map V) (V_map nat) (equiv e_he) (ed_old V V d) (ed_new V V d)) by (apply Hhe_ext; apply Hext_alloc; exact Huf_sort);
           assert (Hnr_old_sort : ~ is_root V V_map V_trie X e_sort (ed_old V V d)) by (intro Hr; apply Hne_d; exact (roots_uf_rel_eq V V_Eqb V_Eqb_ok lt V_default V_map V_map_ok (equiv e_sort) roots_s (ed_old V V d) (ed_new V V d) Hroots_s Hr Hnew_sort Huf_sort));
           assert (Hnr_old_he : map.get (parent (equiv e_he)) (ed_old V V d) <> Some (ed_old V V d)) by (intro Hr; apply Hne_d; exact (roots_uf_rel_eq V V_Eqb V_Eqb_ok lt V_default V_map V_map_ok (equiv e_he) roots_he (ed_old V V d) (ed_new V V d) Hroots_he Hr Hnew_he Huf_he));
           assert (Hhk_old_alloc : Sep.has_key (ed_old V V d) (parent (equiv e_alloc))) by (apply Hkeys_alloc; apply Hmono_eg_sort; exact Hhk_old_inner);
           assert (Heq1 : map.get (parents e_sort) (ed_old V V d) = map.get (parents e_inner) (ed_old V V d)) by (apply HE0; [exact Hhk_old_inner | exact Hnr_old_sort]);
           assert (Heq3 : map.get (parents e_he) (ed_old V V d) = map.get (parents e_alloc) (ed_old V V d)) by (apply HE1; [exact Hhk_old_alloc | exact Hnr_old_he]);
           unfold good_ed;
           split; [rewrite <- Hpar_u; rewrite Heq3; rewrite <- Hpar_alloc; rewrite Heq1; exact Hpar_d |];
           split; [apply Hlift_db_u; exact Hatom_d |];
           split; [eapply all_wkn; [|exact Hargs_d]; intros z _ Hz; exact (Hlift_root_u z (Hkey_ne_tx' z Hz) Hz) |];
           split; [exact Hret_d |];
           split; [exact (Hlift_root_u (ed_new V V d) (Hkey_ne_tx' (ed_new V V d) Hnew_d) Hnew_d) |];
           split; [exact Hne_d |];
           exact (Hlift_uf_u _ _ Huf_d)).
        pose (d_head := {| ed_old := tx'; ed_new := t_v; ed_b := improved; ed_atom := {| atom_fn := sort_of; atom_args := [x']; atom_ret := tx' |} |} : entry_data V V).
        exists (d_head :: ed_tail).
        unfold good_worklist.
        split; [cbn [map]; rewrite Hwl_u; unfold ed_to_entry, d_head; cbn [ed_old ed_new ed_b]; f_equal; rewrite Hwl_he; rewrite <- Hwl_alloc; rewrite Hwl_sort; exact Hwl_tail_eq |].
        split; [constructor; [intro Hin; pose proof (in_all _ _ _ Hall_good_tail Hin) as Hgd; unfold good_ed in Hgd; destruct Hgd as (Hp & _); cbn [ed_old ed_atom d_head] in Hp; apply Htx'_notin_inner; apply Hpke_tail; exists [ed_atom V V d_head]; exact Hp | exact Hnodup_tail] |].
        split; [cbn [all]; split; [unfold good_ed, d_head; cbn [ed_old ed_new ed_b ed_atom atom_fn atom_args atom_ret]; split; [rewrite <- Hpar_u; exact Hpar_tx'_he |]; split; [rewrite <- Hdb_u; exact Htx'_atom |]; split; [cbn [all]; split; [exact (Hothers_u x' Hx'_ne_tx' (Hmono_he x' Hx'_root)) | exact I] |]; split; [reflexivity |]; split; [exact Htv_root_u |]; split; [exact (not_eq_sym Htv_ne_tx') |]; apply Hper_iff; apply Relations.PER_clo_sym; apply Relations.PER_clo_base; right; unfold Relations.singleton_rel; split; reflexivity | apply all_via_in_local; intros d Hd; apply Htail_frame; exact Hd] |].
        split; [intros dj dk Hdj Hdk Hne; cbn [In] in Hdj, Hdk;
          destruct Hdj as [Hdj|Hdj]; destruct Hdk as [Hdk|Hdk] |].
        1: subst dj dk; exfalso; apply Hne; reflexivity.
        1: subst dj.
        1: pose proof (in_all _ _ _ Hall_good_tail Hdk) as Hgk.
        1: unfold good_ed in Hgk.
        1: destruct Hgk as (Hpark & Hatomk & Hargsk & Hretk & Hnewk & Hnek & Hufk).
        1: assert (Hhkk : Sep.has_key (ed_old V V dk) (parent (equiv e_inner))) by (apply Hpke_tail; exists [ed_atom V V dk]; exact Hpark).
        1: assert (Hnewk_he : map.get (parent (equiv e_he)) (ed_new V V dk) = Some (ed_new V V dk)) by (apply Hmono_he; apply Hmono_alloc; apply Hmono_sort; exact Hnewk).
        1: assert (Hufk_he : uf_rel_PER V (V_map V) (V_map nat) (equiv e_he) (ed_old V V dk) (ed_new V V dk)) by (apply Hhe_ext; apply Hext_alloc; apply Hext_sort; exact Hufk).
        1: assert (Hnrk_he : map.get (parent (equiv e_he)) (ed_old V V dk) <> Some (ed_old V V dk)) by (intro Hr; apply Hnek; exact (roots_uf_rel_eq V V_Eqb V_Eqb_ok lt V_default V_map V_map_ok (equiv e_he) roots_he (ed_old V V dk) (ed_new V V dk) Hroots_he Hr Hnewk_he Hufk_he)).
        1: assert (Hatomk_he : atom_in_db V V V_map V_trie X (ed_atom V V dk) (db e_he)) by (apply Hincl_he; rewrite <- Hdb_alloc_eq; exact (Hincl_sort _ Hatomk)).
        1: unfold ed_disjoint, d_head.
        1: cbn [atom_fn atom_args atom_ret ed_atom ed_old ed_new].
        1: split; [intro Hpair; injection Hpair as Hfn Hargs; apply Hx'_notin_inner; apply (is_root_has_key V V_map V_trie X e_inner x'); apply (in_all _ _ _ Hargsk); rewrite Hargs; left; reflexivity |].
        1: split; [intro Heq; apply Htx'_notin_inner; rewrite <- Heq; exact Hhkk |].
        1: split; [intro Heq; apply Hnrk_he; rewrite Heq; exact Htv_root_he |].
        1: intro HH; destruct HH as [Heq|HF]; [apply Hx'_notin_inner; rewrite Heq; exact Hhkk | exact HF].
        1: subst dk.
        1: pose proof (in_all _ _ _ Hall_good_tail Hdj) as Hgj.
        1: unfold good_ed in Hgj.
        1: destruct Hgj as (Hparj & Hatomj & Hargsj & Hretj & Hnewj & Hnej & Hufj).
        1: assert (Hhkj : Sep.has_key (ed_old V V dj) (parent (equiv e_inner))) by (apply Hpke_tail; exists [ed_atom V V dj]; exact Hparj).
        1: assert (Hatomj_he : atom_in_db V V V_map V_trie X (ed_atom V V dj) (db e_he)) by (apply Hincl_he; rewrite <- Hdb_alloc_eq; exact (Hincl_sort _ Hatomj)).
        1: unfold ed_disjoint, d_head.
        1: cbn [atom_fn atom_args atom_ret ed_atom ed_old ed_new].
        1: split; [intro Hpair; injection Hpair as Hfn Hargs; apply Hx'_notin_inner; apply (is_root_has_key V V_map V_trie X e_inner x'); apply (in_all _ _ _ Hargsj); rewrite <- Hargs; left; reflexivity |].
        1: split; [intro Heq; apply Htx'_notin_inner; rewrite Heq; exact Hhkj |].
        1: split; [intro Heq; apply Htx'_notin_inner; rewrite Heq; apply (is_root_has_key V V_map V_trie X e_inner (ed_new V V dj)); exact Hnewj |].
        1: exact (Htx'_not_arg (ed_atom V V dj) Hatomj_he).
        1: exact (Hdisj_tail dj dk Hdj Hdk Hne).
        split; [intros a Ha; destruct (Hdb_u_inv a Ha) as [Hargs_roots _]; split; [exact Hargs_roots | intro HF; destruct HF] |].
        intros b Hb_u Hnr.
        rewrite <- Hdb_u in Hb_u.
        destruct (HR b Hb_u) as [Hbeq | Hb_alloc].
        1: exists d_head.
        1: cbn [In]; split; [left; reflexivity|].
        1: subst b; unfold d_head; cbn [ed_atom atom_fn atom_args]; split; reflexivity.
        1: rewrite <- Hdb_alloc_eq in Hb_alloc.
        1: pose proof (V_Eqb_ok (atom_fn b) sort_of) as Heqb_case.
        1: destruct (eqb (atom_fn b) sort_of) eqn:Heqb.
        1: assert (Hfn : atom_fn b = sort_of) by exact Heqb_case.
        1: pose proof (HN b Hb_alloc Hfn) as Hb_inner.
        1: assert (Hnr_inner : ~ Semantics.is_root V V V_map V_map V_trie X e_inner (atom_ret b)) by (intro Hr_inner; apply Hnr; exact (Hlift_root_u (atom_ret b) (Hkey_ne_tx' (atom_ret b) Hr_inner) Hr_inner)).
        1: destruct (Hcov_tail b Hb_inner Hnr_inner) as (d & Hd_in & Hd_fn & Hd_args).
        1: exists d.
        1: cbn [In].
        1: split; [right; exact Hd_in |].
        1: split; [exact Hd_fn | exact Hd_args].
        1: assert (Hfn_ne : atom_fn b <> sort_of) by exact Heqb_case.
        1: destruct (Hdb_sort b Hb_alloc) as (Hargs_roots_b & Hretb).
        1: specialize (Hretb Hfn_ne).
        1: assert (Hretb_ne_tx' : atom_ret b <> tx') by (intro Heqtx; apply Htx'_fresh; rewrite <- Heqtx; apply Hkeys_alloc; apply (is_root_has_key V V_map V_trie X e_sort (atom_ret b)); exact Hretb).
        1: exfalso.
        1: apply Hnr.
        1: apply Hothers_u; [exact Hretb_ne_tx' | apply Hmono_he; apply Hmono_alloc; exact Hretb].
    Qed.

    (* Simple-form corollary: the consumer interface (matches the
       [W]-rewiring stub).  Instantiate the vc-form at [empty_egraph]
       and discharge the six invariant hypotheses vacuously (empty db /
       parents / analyses / worklist, ok union-find), extracting the
       good_worklist witness. *)
    Lemma add_ctx_good_worklist c (Hwfc : wf_ctx l c)
      : exists ed_list,
          good_worklist V V V_map V_map V_trie X
            (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
            ed_list.
    Proof.
      pose proof (add_ctx_good_worklist_vc c Hwfc) as Hvc.
      unfold vc in Hvc.
      set (e0 := @empty_egraph V V_default V V_map V_map V_trie X) in *.
      specialize (Hvc e0).
      (* hyp 1: union-find ok *)
      assert (Huf0 : exists roots,
                 union_find_ok lt (Defs.equiv e0) roots).
      { exact (ex_intro _ [] (@union_find_empty_ok V lt succ V_default V_map V_map_ok)). }
      (* hyp 2: db_inv(True) — empty db *)
      assert (Hdb0 : @db_inv V V V_map V_map V_trie X (fun _ => True) e0).
      { intros aa Hin. exfalso.
        unfold Semantics.atom_in_db in Hin.
        unfold e0 in Hin. cbn [Defs.db empty_egraph] in Hin.
        rewrite map.get_empty in Hin. exact Hin. }
      (* hyp 3: egraph_ok — from empty_sound_for_interpretation *)
      assert (Hok0 : egraph_ok V lt V V_map V_map V_trie X e0).
      { exact (proj1 (@empty_sound_for_interpretation V lt succ V_default V V_map V_map_ok
                        V_map V_map_ok V_trie X lang_model)). }
      (* hyp 4: parents_keys_in_equiv — empty parents *)
      assert (Hpke0 : parents_keys_in_equiv V V V_map V_map V_trie X e0).
      { intros y [s Hs]. unfold e0 in Hs. cbn [parents empty_egraph] in Hs.
        rewrite map.get_empty in Hs. discriminate. }
      (* hyp 5: analyses_cover — empty union-find parent map *)
      assert (Hac0 : SemanticsAnalysesCover.analyses_cover V V V_map V_map V_trie X e0).
      { intros z Hz. exfalso. unfold Sep.has_key in Hz. unfold e0 in Hz.
        cbn [equiv empty_egraph UnionFind.parent UnionFind.empty] in Hz.
        rewrite map.get_empty in Hz. exact Hz. }
      (* hyp 6: worklist empty *)
      assert (Hwl0 : Defs.worklist e0 = []).
      { reflexivity. }
      specialize (Hvc Huf0 Hdb0 Hok0 Hpke0 Hac0 Hwl0).
      destruct Hvc as (_ & _ & _ & _ & _ & _ & _ & Hgwl).
      exact Hgwl.
    Qed.

  End AddCtxInvert.
End WithVar.
