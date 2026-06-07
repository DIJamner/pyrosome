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
From Pyrosome.Tools.EGraph Require Import CtxReadback.


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
  Local Notation ctx_readback_to_eF := (@CtxReadback.ctx_readback_to_eF V V_Eqb V_default V_map V_trie sort_of).
  Local Notation ctx_readback_wf_subst := (@CtxReadback.ctx_readback_wf_subst V V_Eqb V_Eqb_ok V_default V_map V_trie sort_of).

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
                      fuel e1 ed_list Hok Hgwl) as [HdbT [Hmono _] ].
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
    (* Structural lemma: the rebuilt egraph satisfies ctx_readback_eF.
       This is the pure structural core of add_ctx_inversion, factored
       out so the conclusion-construction side (B0) can consume it
       directly without re-proving the rebuild/survival chain. *)
    Lemma add_ctx_readback_eF (rf : nat) c
      : wf_ctx l c ->
        (exists ed_list, good_worklist V V V_map V_map V_trie X
           (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))) ed_list) ->
        fst (rebuild rf (snd (add_ctx succ sort_of l false false c
                                (empty_egraph V_default X)))) = Result.Success tt ->
        @CtxReadback.ctx_readback_eF V _ _ V_map V_trie sort_of X
          (snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))
          (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
          c.
    Proof.
      intros Hwfc Hgwl Hsucc.
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
      exact Hrbef.
    Qed.

    (* ============================================================ *)
    (* assum_db_frame_eF: transports the PRE-rebuild exhaustiveness   *)
    (* frame (assum_db_frame_pre) to the POST-rebuild egraph, for     *)
    (* non-sort_of atoms.  Given b ∈ eF with b.fn ≠ sort_of, we      *)
    (* recover x, n_x, s_x, xs_x witnessing the sort-skeleton tree   *)
    (* and node derivation in eF.                                     *)
    Lemma assum_db_frame_eF (rf : nat) c
      (Hwfc : wf_ctx l c)
      (Hgwl : exists ed_list, good_worklist V V V_map V_map V_trie X
                (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                ed_list)
      (Hsucc : fst (rebuild rf (snd (add_ctx succ sort_of l false false c
                                (empty_egraph V_default X))))
               = Result.Success tt)
      : forall b,
          ain b (snd (rebuild rf (snd (add_ctx succ sort_of l false false c
                                         (empty_egraph V_default X))))) ->
          b.(atom_fn) <> sort_of ->
          exists x n_x s_x xs_x,
            In (x, scon n_x s_x) c
            /\ atom_tree_sort V V_map V_trie X
                 (snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))
                 (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                 (scon n_x s_x) xs_x
            /\ atom_node V V_map V_trie X
                 (snd (rebuild rf (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))
                 (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                 (con n_x s_x) xs_x b.
    Proof.
      intros b Hb Hbfn.
      change (empty_egraph V_default X)
        with (@empty_egraph V V_default V V_map V_map V_trie X) in *.
      set (e0 := @empty_egraph V V_default V V_map V_map V_trie X) in *.
      set (sub := fst (add_ctx succ sort_of l false false c e0)) in *.
      set (e1 := snd (add_ctx succ sort_of l false false c e0)) in *.
      set (eF := snd (rebuild rf e1)) in *.
      (* --- base facts at empty_egraph --- *)
      assert (Hok0 : egraph_ok e0)
        by exact (proj1 (@empty_sound_for_interpretation V lt succ V_default V V_map V_map_ok
                           V_map V_map_ok V_trie X lang_model)).
      assert (Huf0 : exists roots, union_find_ok lt (Defs.equiv e0) roots)
        by exact (ex_intro _ [] (@union_find_empty_ok V lt succ V_default V_map V_map_ok)).
      assert (Hdb0 : db_ctx_inv X e0)
        by (intros aa Hin; exfalso;
            unfold Semantics.atom_in_db in Hin;
            unfold e0 in Hin; cbn [Defs.db empty_egraph] in Hin;
            rewrite map.get_empty in Hin; exact Hin).
      (* --- add_ctx_egraph_ok: structural envelope --- *)
      pose proof (@Theorems.add_ctx_egraph_ok V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as HE.
      unfold vc in HE. specialize (HE e0).
      fold sub e1 in HE.
      specialize (HE Huf0 Hdb0 Hok0).
      destruct HE as (Huf1 & Hdb1 & Hroots1 & Hmapfst & Hok1).
      (* --- assum_db_frame_pre: PRE-rebuild exhaustiveness frame --- *)
      pose proof (@Theorems.assum_db_frame_pre V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as Hframe_vc.
      unfold vc in Hframe_vc. specialize (Hframe_vc e0).
      fold sub e1 in Hframe_vc.
      assert (He0_sortof : forall a, ain a e0 -> a.(atom_fn) = sort_of)
        by (intros a Ha; exfalso;
            unfold ain, Semantics.atom_in_egraph, Semantics.atom_in_db in Ha;
            unfold e0 in Ha; cbn [Defs.db empty_egraph] in Ha;
            rewrite map.get_empty in Ha; exact Ha).
      specialize (Hframe_vc Huf0 Hdb0 He0_sortof).
      (* Hframe_vc : forall a ∈ e1, a.fn ≠ sort_of →
           ∃ x n_x s_x xs_x. In ... /\ atom_tree_sort X e1 sub ... /\ atom_node X e1 sub ... a *)
      (* --- rebuild_canon: 3-conjunct including reverse image --- *)
      destruct rf as [|fuel].
      { exfalso. cbn in Hsucc. discriminate Hsucc. }
      destruct Hgwl as [ed_list Hgwl].
      pose proof (@rebuild_canon V V_Eqb V_Eqb_ok lt succ V_default
                    V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                    X _ lang_model (lang_model_ok l Hsof Hwf)
                    fuel e1 ed_list Hok1 Hgwl) as (HdbT & Hmono & Hrev).
      (* --- canonicalizing survival --- *)
      pose proof (rebuild_survives_canonical e1 (S fuel) Hok1 (ex_intro _ _ Hgwl) Hsucc) as Hsurv.
      (* --- build Hsurv_exact from Hsurv (for use with atom_tree_sort_survives) --- *)
      assert (Hrefl : forall xl,
                 all (is_root X e1) xl ->
                 all2 (UnionFind.uf_rel_PER V (V_map V) (V_map nat) (Defs.equiv e1)) xl xl)
        by (induction xl as [|z xl IHxl]; cbn; [trivial|];
            intros [Hz Hxl]; split; [apply Relations.PER_clo_base; exact Hz | apply IHxl; exact Hxl]).
      assert (Hsurv_exact : forall a0 : atom,
                 ain a0 e1 ->
                 all (is_root X e1) (atom_args a0) ->
                 is_root X e1 (atom_ret a0) ->
                 ain a0 eF)
        by (intros a0 Ha0_in Ha0_args Ha0_ret;
            apply Hsurv; [ | exact Ha0_args | exact Ha0_ret ];
            exists a0; split; [| exact Ha0_in];
            unfold Semantics.atom_canonical_equiv; split; [reflexivity|]; split;
            [apply Hrefl; exact Ha0_args | apply Relations.PER_clo_base; exact Ha0_ret]).
      (* --- reverse image: b ∈ eF → a ∈ e1 with same fn+args --- *)
      unfold ain, Semantics.atom_in_egraph in Hb. fold eF in Hb.
      destruct (Hrev b Hb) as (a & Ha_e1_db & Hafn & Haargs).
      assert (Ha_e1_in : ain a e1) by (unfold ain, Semantics.atom_in_egraph; exact Ha_e1_db).
      assert (Hafn_ne : atom_fn a <> sort_of) by (rewrite Hafn; exact Hbfn).
      (* --- apply pre-frame to a --- *)
      destruct (Hframe_vc a Ha_e1_in Hafn_ne) as (x & n_x & s_x & xs_x & Hxin & Htree_e1 & Hnode_e1).
      (* --- wf_sort for the sort skeleton --- *)
      pose proof (@Core.in_ctx_wf V V_Eqb V_Eqb_ok l c x (scon n_x s_x) Hwf Hwfc Hxin) as Hwst.
      (* --- fold e1/sub for transport lemmas --- *)
      fold e1 sub in Htree_e1, Hnode_e1.
      (* --- transport atom_tree_sort from e1 to eF --- *)
      pose proof (@Theorems.atom_tree_sort_survives V V_Eqb V_default V_map V_trie sort_of X l Hsof
                    e1 eF sub c Hdb1 Hsurv_exact (scon n_x s_x) Hwst xs_x Htree_e1) as Htree_eF.
      (* --- transport atom_node_sort from e1 to eF --- *)
      pose proof (@Theorems.atom_node_sort_survives V V_Eqb V_default V_map V_trie sort_of X l Hsof
                    e1 eF sub c Hdb1 Hsurv_exact n_x s_x Hwst xs_x a Hnode_e1) as Hnode_eF_a.
      (* --- determinism: extract a ∈ eF.db from atom_node, then a = b --- *)
      assert (Ha_eF_in : atom_in_db V V V_map V_trie X a (db eF))
        by (clear - Hnode_eF_a;
            induction Hnode_eF_a as [n0 s0 sids0 xe0 HF2_0 Hain0
                                    | n0 s0 sids0 xe0 si0 sid0 a0 HF2_0 Hain0 Hcomb0 Hnode0 IH0];
            [unfold Semantics.atom_in_egraph in Hain0; exact Hain0 | exact IH0]).
      assert (Hret_eq : atom_ret a = atom_ret b)
        by (unfold Semantics.atom_in_db, "<$>", Is_Some_satisfying in Ha_eF_in, Hb;
            rewrite Hafn, Haargs in Ha_eF_in;
            destruct (map.get (Defs.db eF) (atom_fn b)) as [tbl|];
              cbn in Ha_eF_in, Hb; [|contradiction];
            destruct (map.get tbl (atom_args b)) as [entry|];
              cbn in Ha_eF_in, Hb; [|contradiction];
            congruence).
      assert (Hab : a = b)
        by (destruct a as [afn aargs aret]; destruct b as [bfn bargs bret];
            cbn [atom_fn atom_args atom_ret] in *; subst; reflexivity).
      (* --- conclude --- *)
      exists x, n_x, s_x, xs_x.
      split; [exact Hxin|].
      split; [exact Htree_eF|].
      rewrite <- Hab. exact Hnode_eF_a.
    Qed.

    (* POST-rebuild sort_of frame: every sort_of atom of eF has its single
       argument equal to a ctx-var companion (a [sub] entry).  Transport of
       [assum_sortof_frame_pre] to eF via [rebuild_canon]'s reverse image
       (the companion arg is a root, so its canonical image is itself). *)
    Lemma assum_sortof_frame_eF (rf : nat) c
      (Hwfc : wf_ctx l c)
      (Hgwl : exists ed_list, good_worklist V V V_map V_map V_trie X
                (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                ed_list)
      (Hsucc : fst (rebuild rf (snd (add_ctx succ sort_of l false false c
                                (empty_egraph V_default X))))
               = Result.Success tt)
      : forall b,
          ain b (snd (rebuild rf (snd (add_ctx succ sort_of l false false c
                                         (empty_egraph V_default X))))) ->
          b.(atom_fn) = sort_of ->
          exists nm x', b.(atom_args) = [x'] /\
            In (nm, x') (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))).
    Proof.
      intros b Hb Hbfn.
      change (empty_egraph V_default X)
        with (@empty_egraph V V_default V V_map V_map V_trie X) in *.
      set (e0 := @empty_egraph V V_default V V_map V_map V_trie X) in *.
      set (sub := fst (add_ctx succ sort_of l false false c e0)) in *.
      set (e1 := snd (add_ctx succ sort_of l false false c e0)) in *.
      set (eF := snd (rebuild rf e1)) in *.
      assert (Hok0 : egraph_ok e0)
        by exact (proj1 (@empty_sound_for_interpretation V lt succ V_default V V_map V_map_ok
                           V_map V_map_ok V_trie X lang_model)).
      assert (Huf0 : exists roots, union_find_ok lt (Defs.equiv e0) roots)
        by exact (ex_intro _ [] (@union_find_empty_ok V lt succ V_default V_map V_map_ok)).
      assert (Hdb0 : db_ctx_inv X e0)
        by (intros aa Hin; exfalso;
            unfold Semantics.atom_in_db in Hin;
            unfold e0 in Hin; cbn [Defs.db empty_egraph] in Hin;
            rewrite map.get_empty in Hin; exact Hin).
      pose proof (@Theorems.add_ctx_egraph_ok V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as HE.
      unfold vc in HE. specialize (HE e0).
      fold sub e1 in HE.
      specialize (HE Huf0 Hdb0 Hok0).
      destruct HE as (Huf1 & Hdb1 & Hroots1 & Hmapfst & Hok1).
      pose proof (@Theorems.assum_sortof_frame_pre V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as Hsf_vc.
      unfold vc in Hsf_vc. specialize (Hsf_vc e0).
      fold sub e1 in Hsf_vc.
      assert (He0_nosof : forall a, ain a e0 -> a.(atom_fn) <> sort_of)
        by (intros a Ha; exfalso;
            unfold ain, Semantics.atom_in_egraph, Semantics.atom_in_db in Ha;
            unfold e0 in Ha; cbn [Defs.db empty_egraph] in Ha;
            rewrite map.get_empty in Ha; exact Ha).
      specialize (Hsf_vc Huf0 Hdb0 He0_nosof).
      destruct rf as [|fuel].
      { exfalso. cbn in Hsucc. discriminate Hsucc. }
      destruct Hgwl as [ed_list Hgwl].
      pose proof (@rebuild_canon V V_Eqb V_Eqb_ok lt succ V_default
                    V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                    X _ lang_model (lang_model_ok l Hsof Hwf)
                    fuel e1 ed_list Hok1 Hgwl) as (HdbT & Hmono & Hrev).
      unfold ain, Semantics.atom_in_egraph in Hb. fold eF in Hb.
      destruct (Hrev b Hb) as (a & Ha_e1_db & Hafn & Haargs).
      assert (Ha_e1_in : ain a e1) by (unfold ain, Semantics.atom_in_egraph; exact Ha_e1_db).
      assert (Hafn_sof : atom_fn a = sort_of) by (rewrite Hafn; exact Hbfn).
      destruct (Hsf_vc a Ha_e1_in Hafn_sof) as (nm & x' & Hargs_a & Hin_sub).
      exists nm, x'. split; [ rewrite <- Haargs; exact Hargs_a | exact Hin_sub ].
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

    (* [_gen] port over [add_ctx_gen].  The non-skip cons branch is the
       original proof verbatim; the skip branch runs only [alloc_opaque],
       which leaves db / parents / worklist unchanged and preserves roots /
       equiv, so all 8 conjuncts lift from the tail (the [good_worklist]
       ed_list is the tail's, unchanged). *)
    Lemma add_ctx_good_worklist_vc_gen (no_sort : V -> bool) c
      : wf_ctx l c ->
        vc (add_ctx_gen succ sort_of l false false no_sort c)
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
      intros Hctx. unfold add_ctx_gen. induction c as [|[name t] c' IH].
      - (* nil case: identical to add_ctx_good_worklist_vc *)
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
      - (* cons case *)
        cbn [list_Mfoldr]. eapply vc_bind.
        { apply IH. inversion Hctx; assumption. }
        intros e_pre base'. cbn [Mbind StateMonad.state_monad Mret].
        destruct (no_sort name) eqn:Hns.
        2:{
        cbn [Mbind StateMonad.state_monad Mret].
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
        (* ---- final assembly ---- *)
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
        }
        (* ===== SKIP branch: only alloc_opaque runs ===== *)
        cbn [Mbind StateMonad.state_monad Mret].
        unfold vc; intros e_inner Htail.
        intros Hok Hdb Hok_eg Hpke Hac Hwl.
        specialize (Htail Hok Hdb Hok_eg Hpke Hac Hwl).
        assert (Hwfc' : wf_ctx l c') by (inversion Hctx; assumption).
        destruct Htail as (Huf_tail & Hdb_tail & Hall_tail & Hfst_tail & Hok_eg_tail & Hpke_tail & Hac_tail & Hgwl_tail).
        pose proof (@alloc_opaque_rank_zero V V_Eqb V_Eqb_ok lt succ V V_map V_map V_map_ok V_trie X HX lt_asymmetric lt_succ lt_trans) as Halloc.
        pose proof (@alloc_opaque_egraph_ok V V_Eqb V_Eqb_ok lt succ V V_map V_map V_map_ok V_trie X HX lt_asymmetric lt_succ lt_trans) as Halloc_eg.
        pose proof (@alloc_opaque_parents_keys_in_equiv V V_Eqb V_Eqb_ok lt succ V V_map V_map V_map_ok V_trie X HX lt_asymmetric lt_succ lt_trans) as Halloc_pke.
        pose proof (@alloc_opaque_analyses_cover V V_Eqb V_Eqb_ok lt succ V V_map V_map V_map_ok V_trie X HX lt_asymmetric lt_succ lt_trans) as Halloc_ac.
        unfold vc in Halloc, Halloc_eg, Halloc_pke, Halloc_ac.
        specialize (Halloc e_inner). specialize (Halloc_eg e_inner). specialize (Halloc_pke e_inner). specialize (Halloc_ac e_inner).
        destruct (alloc_opaque V succ V V_map V_map V_trie X e_inner) as [x' e_alloc] eqn:Heq_alloc.
        cbn [fst snd] in Halloc, Halloc_eg, Halloc_pke, Halloc_ac.
        destruct Huf_tail as [roots_t Hroots_t].
        specialize (Halloc roots_t Hroots_t).
        destruct Halloc as (Hok_alloc & Hfresh_x' & Hx'_root & Hx'_rank0 & Hkeys_alloc & Hmono_alloc & Hdb_alloc_eq & Hpar_alloc & Hwl_alloc).
        specialize (Halloc_eg Hok_eg_tail).
        destruct Halloc_eg as (Hok_eg_alloc & _ & Hx'_key_alloc & Hmono_eg_alloc & _ & _ & _).
        specialize (Halloc_pke Hok_eg_tail Hpke_tail).
        specialize (Halloc_ac Hok_eg_tail Hac_tail).
        destruct Halloc_ac as (Hac_alloc & Hax'_analysis).
        cbn [fst snd] in *.
        (* db_ctx_inv e_alloc from tail (db unchanged) *)
        assert (Hdb_alloc : db_ctx_inv V V_map V_trie sort_of X e_alloc) by
          (unfold db_ctx_inv, db_inv in *; intros a Ha; rewrite <- Hdb_alloc_eq in Ha;
           specialize (Hdb_tail a Ha); destruct Hdb_tail as [Hargs_roots Hret_root]; split;
           [ eapply all_wkn; [|exact Hargs_roots]; intros z _ Hz; exact (Hmono_alloc z Hz)
           | intro HPfn; exact (Hmono_alloc _ (Hret_root HPfn)) ]).
        assert (Hext_alloc : equiv_extends V V V_map V_map V_trie X e_inner e_alloc) by
          (pose proof (@alloc_opaque_parent_eq V V_map V_trie succ X HX e_inner) as Hpar_in;
           cbn [fst snd] in Hpar_in; rewrite Heq_alloc in Hpar_in; cbn [fst snd] in Hpar_in;
           assert (Hnone_x' : map.get (parent (Defs.equiv e_inner)) x' = None) by
             (unfold Sep.has_key in Hfresh_x'; destruct (map.get (parent (Defs.equiv e_inner)) x'); tauto);
           unfold equiv_extends, uf_rel_PER; intros i j Hpre; rewrite Hpar_in;
           eapply uf_rel_PER_alloc_monotone; [exact V_map_ok | exact Hnone_x' | unfold uf_rel_PER; exact Hpre]).
        cbn [fst snd].
        split; [exact (ex_intro _ _ Hok_alloc)|].
        split; [exact Hdb_alloc|].
        split.
        { cbn [all]. split.
          - exact Hx'_root.
          - eapply all_wkn; [|exact Hall_tail]. intros [xn yn] _ Hyn_root.
            cbn [snd] in *. exact (Hmono_alloc _ Hyn_root). }
        split; [cbn [map fst]; f_equal; exact Hfst_tail|].
        split; [exact Hok_eg_alloc|].
        split; [exact Halloc_pke|].
        split; [exact Hac_alloc|].
        (* good_worklist e_alloc: the tail's ed_list, lifted (db/parents/worklist unchanged, roots/uf preserved) *)
        destruct Hgwl_tail as [ed_tail Hgood_tail].
        unfold good_worklist in Hgood_tail.
        destruct Hgood_tail as (Hwl_tail_eq & Hnodup_tail & Hall_good_tail & Hdisj_tail & Hdbfalse_tail & Hcov_tail).
        assert (Hx'_notin_inner : ~ Sep.has_key x' (parent (equiv e_inner))) by exact Hfresh_x'.
        assert (Hlift_root_a : forall z, map.get (parent (equiv e_inner)) z = Some z -> map.get (parent (equiv e_alloc)) z = Some z) by exact Hmono_alloc.
        exists ed_tail.
        unfold good_worklist.
        split; [rewrite <- Hwl_alloc; exact Hwl_tail_eq |].
        split; [exact Hnodup_tail |].
        split.
        { apply all_via_in_local; intros d Hd_in.
          pose proof (in_all _ _ _ Hall_good_tail Hd_in) as Hd.
          unfold good_ed in Hd |- *.
          destruct Hd as (Hpar_d & Hatom_d & Hargs_d & Hret_d & Hnew_d & Hne_d & Huf_d).
          split; [rewrite <- Hpar_alloc; exact Hpar_d |].
          split; [unfold atom_in_db in Hatom_d |- *; rewrite <- Hdb_alloc_eq; exact Hatom_d |].
          split; [eapply all_wkn; [|exact Hargs_d]; intros z _ Hz; exact (Hlift_root_a z Hz) |].
          split; [exact Hret_d |].
          split; [exact (Hlift_root_a (ed_new V V d) Hnew_d) |].
          split; [exact Hne_d |].
          apply Hext_alloc; exact Huf_d. }
        split; [exact Hdisj_tail |].
        split.
        { intros a Ha. unfold atom_in_db in Ha. rewrite <- Hdb_alloc_eq in Ha.
          destruct (Hdbfalse_tail a Ha) as [Hargs _]. split.
          - eapply all_wkn; [|exact Hargs]; intros z _ Hz; exact (Hmono_alloc z Hz).
          - intro HF; destruct HF. }
        intros b Hb_a Hnr.
        unfold atom_in_db in Hb_a. rewrite <- Hdb_alloc_eq in Hb_a.
        assert (Hnr_inner : ~ Semantics.is_root V V V_map V_map V_trie X e_inner (atom_ret b)) by
          (intro Hr; apply Hnr; unfold Semantics.is_root in Hr |- *; exact (Hmono_alloc _ Hr)).
        destruct (Hcov_tail b Hb_a Hnr_inner) as (d & Hd_in & Hd_fn & Hd_args).
        exists d. split; [exact Hd_in|]. split; [exact Hd_fn | exact Hd_args].
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

    Lemma good_worklist_eq_assum c e1 t (Hwfc : wf_ctx l c) (Hwfe1 : wf_term l c e1 t)
      : exists ed_list,
          good_worklist V V V_map V_map V_trie X
            (snd (add_open_term succ sort_of l false false
                    (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                    e1
                    (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))
            ed_list.
    Proof.
      (* Step 1: extract all facts from add_ctx_good_worklist_vc at empty_egraph *)
      pose proof (add_ctx_good_worklist_vc c Hwfc) as Hvc.
      unfold vc in Hvc.
      set (e0 := @empty_egraph V V_default V V_map V_map V_trie X) in *.
      specialize (Hvc e0).
      assert (Huf0 : exists roots, union_find_ok lt (Defs.equiv e0) roots).
      { exact (ex_intro _ [] (@union_find_empty_ok V lt succ V_default V_map V_map_ok)). }
      assert (Hdb0 : @db_inv V V V_map V_map V_trie X (fun _ => True) e0).
      { intros aa Hin. exfalso. unfold Semantics.atom_in_db in Hin.
        unfold e0 in Hin. cbn [Defs.db empty_egraph] in Hin.
        rewrite map.get_empty in Hin. exact Hin. }
      assert (Hok0 : egraph_ok V lt V V_map V_map V_trie X e0).
      { exact (proj1 (@empty_sound_for_interpretation V lt succ V_default V V_map V_map_ok
                        V_map V_map_ok V_trie X lang_model)). }
      assert (Hpke0 : parents_keys_in_equiv V V V_map V_map V_trie X e0).
      { intros y [s Hs]. unfold e0 in Hs. cbn [parents empty_egraph] in Hs.
        rewrite map.get_empty in Hs. discriminate. }
      assert (Hac0 : SemanticsAnalysesCover.analyses_cover V V V_map V_map V_trie X e0).
      { intros z Hz. exfalso. unfold Sep.has_key in Hz. unfold e0 in Hz.
        cbn [equiv empty_egraph UnionFind.parent UnionFind.empty] in Hz.
        rewrite map.get_empty in Hz. exact Hz. }
      assert (Hwl0 : Defs.worklist e0 = []).
      { reflexivity. }
      specialize (Hvc Huf0 Hdb0 Hok0 Hpke0 Hac0 Hwl0).
      destruct Hvc as (Huf1 & Hdb1 & Hroots1 & Hmapfst & Hok1 & Hpke1 & Hac1 & [ed_list Hgw]).
      set (sub := fst (add_ctx succ sort_of l false false c e0)) in *.
      set (e_ctx := snd (add_ctx succ sort_of l false false c e0)) in *.
      set (e_open := snd (add_open_term succ sort_of l false false sub e1 e_ctx)).
      exists ed_list.
      unfold good_worklist in Hgw.
      destruct Hgw as (Hwl_eq & Hnodup & Hall_good & Hdisj & Hdbfalse & Hcov).
      (* Step 2: apply add_open_term_all_roots → roots_env e_ctx e_open *)
      assert (Hmapfst' : map fst c = map fst sub) by (symmetry; exact Hmapfst).
      pose proof (@Theorems.add_open_term_all_roots V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                    c sub e1 t Hwfe1 Hwfc Hmapfst') as Hroots.
      unfold vc in Hroots. specialize (Hroots e_ctx).
      fold e_open in Hroots.
      unfold Theorems.open_roots_post in Hroots.
      specialize (Hroots Huf1 Hdb1 Hroots1).
      fold e_open in Hroots.
      destruct Hroots as (Henv & _).
      unfold Theorems.roots_env in Henv.
      destruct Henv as (Huf_open & Hdb_open_ctx & Hdb_incl & Hroots_mono).
      (* Step 3: apply add_open_worklist_frame → worklist preserved, egraph_ok *)
      assert (Hbase_keys : all (fun p => Sep.has_key (snd p) (parent (Defs.equiv e_ctx))) sub).
      { eapply all_wkn; [| exact Hroots1].
        intros p _ Hp. apply (Theorems.is_root_has_key V V_map V_trie X e_ctx (snd p)). exact Hp. }
      pose proof (@Theorems.add_open_worklist_frame V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf
                    l (add_open_sort succ sort_of l false false) Hwf (incl_refl l)
                    c Hwfc) as Hwlf.
      pose proof (proj1 Hwlf e1 t Hwfe1 sub Hmapfst') as Hwlf_term.
      unfold vc in Hwlf_term. specialize (Hwlf_term e_ctx).
      unfold Theorems.open_wlframe_post in Hwlf_term.
      specialize (Hwlf_term Hok1 Hac1 Hbase_keys).
      fold e_open in Hwlf_term.
      destruct Hwlf_term as (Hwl_open & Hok_open & _ & Hmono_key & _).
      unfold add_open_term in e_open.
      fold e_open in Hwl_open.
      fold e_open in Hok_open.
      fold e_open in Hmono_key.
      (* Step 4: apply add_open_node_atoms → equiv_extends e_ctx e_open *)
      pose proof (@Theorems.add_open_node_atoms V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                    l (add_open_sort succ sort_of l false false) Hwf (incl_refl l)
                    c Hwfc) as Hnodes.
      pose proof (proj1 Hnodes e1 t Hwfe1 sub Hmapfst') as Hnode_term.
      unfold vc in Hnode_term. specialize (Hnode_term e_ctx).
      unfold Theorems.open_atomtree_post in Hnode_term.
      specialize (Hnode_term Huf1 Hdb1 Hroots1).
      cbn [fst snd] in Hnode_term.
      fold e_open in Hnode_term.
      destruct Hnode_term as (_ & _ & _ & Hext).
      (* Step 5: apply add_open_parents_frame → parents preserved for non-root keys *)
      pose proof (@Theorems.add_open_parents_frame V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                    l (add_open_sort succ sort_of l false false) Hwf (incl_refl l)
                    c Hwfc) as Hpf.
      pose proof (proj1 Hpf e1 t Hwfe1 sub Hmapfst') as Hpf_term.
      unfold vc in Hpf_term. specialize (Hpf_term e_ctx).
      fold e_open in Hpf_term.
      unfold Theorems.open_parents_frame_post in Hpf_term.
      fold e_open in Hpf_term.
      specialize (Hpf_term Hok1 Huf1 Hdb1 Hroots1).
      (* Step 6: assemble good_worklist e_open ed_list *)
      unfold good_worklist.
      split.
      { (* (1) worklist e_open = map (ed_to_entry) ed_list *)
        rewrite Hwl_open. exact Hwl_eq. }
      split.
      { (* (2) NoDup ed_list: egraph-independent *)
        exact Hnodup. }
      split.
      { (* (3) all (good_ed e_open) ed_list *)
        apply all_via_in_local. intros d Hd_in.
        pose proof (in_all _ _ _ Hall_good Hd_in) as Hgd.
        unfold good_ed in Hgd |- *.
        destruct Hgd as (Hpar_d & Hatom_d & Hargs_d & Hret_d & Hnew_d & Hne_d & Huf_d).
        assert (Hhk_old : Sep.has_key (ed_old V V d) (parent (Defs.equiv e_ctx))).
        { apply Hpke1. exists [ed_atom V V d]. exact Hpar_d. }
        assert (Hnew_open : map.get (parent (Defs.equiv e_open)) (ed_new V V d) = Some (ed_new V V d)).
        { exact (Hroots_mono (ed_new V V d) Hnew_d). }
        assert (Huf_open_d : uf_rel_PER V (V_map V) (V_map nat) (Defs.equiv e_open) (ed_old V V d) (ed_new V V d)).
        { exact (Hext (ed_old V V d) (ed_new V V d) Huf_d). }
        (* ed_old d is NOT a root in e_open: if it were, roots_uf_rel_eq → ed_old=ed_new, contradiction *)
        assert (Hnr_old_open : ~ Semantics.is_root V V V_map V_map V_trie X e_open (ed_old V V d)).
        { intro Hroot_old.
          destruct Huf_open as [roots_open Hroots_open].
          exact (Hne_d (@Semantics.roots_uf_rel_eq V V_Eqb V_Eqb_ok lt V_default V_map V_map_ok
                          (Defs.equiv e_open) roots_open (ed_old V V d) (ed_new V V d) Hroots_open
                          Hroot_old Hnew_open Huf_open_d)). }
        split.
        { rewrite (Hpf_term (ed_old V V d) Hhk_old Hnr_old_open). exact Hpar_d. }
        split. { exact (Hdb_incl (ed_atom V V d) Hatom_d). }
        split. { eapply all_wkn; [| exact Hargs_d]. intros z _ Hz. exact (Hroots_mono z Hz). }
        split. { exact Hret_d. }
        split. { exact Hnew_open. }
        split. { exact Hne_d. }
        { exact Huf_open_d. } }
      split.
      { (* (4) ed_disjoint: egraph-independent, carry over verbatim *)
        exact Hdisj. }
      split.
      { (* (5) db_inv(False) e_open: from db_ctx_inv e_open *)
        unfold db_inv. intros a Ha.
        destruct (Hdb_open_ctx a Ha) as [Hargs_roots _].
        split; [exact Hargs_roots | intro HF; destruct HF]. }
      { (* (6) coverage *)
        intros b Hb_open Hnr_open.
        (* atom_fn b ≠ sort_of → db_ctx_inv gives ret is root → contradicts Hnr_open → fn = sort_of *)
        assert (Hfn_eq : atom_fn b = sort_of).
        { destruct (Hdb_open_ctx b Hb_open) as [_ Hret_root].
          pose proof (V_Eqb_ok (atom_fn b) sort_of) as Heqb_case.
          destruct (eqb (atom_fn b) sort_of) eqn:Heqb.
          - exact Heqb_case.
          - exfalso. apply Hnr_open. exact (Hret_root Heqb_case). }
        (* fn = sort_of → b ∈ e_ctx.db (add_open_term keeps sort_of sub-trie unchanged) *)
        assert (Hb_ctx : atom_in_db V V V_map V_trie X b (Defs.db e_ctx)).
        { pose proof (@Theorems.add_open_term'_keeps_sortof V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                        V_trie succ sort_of lt X HX l Hsof
                        (add_open_sort succ sort_of l false false)
                        (fun sub0 t0 e => @Theorems.add_open_sort'_keeps_sortof V V_Eqb V_Eqb_ok V_default
                                           V_map V_map_ok V_trie succ sort_of lt X HX l Hsof
                                           (S (length l)) sub0 t0 e)
                        sub e1 e_ctx) as Hkeeps.
          unfold Semantics.atom_in_db, Is_Some_satisfying in Hb_open |- *.
          rewrite Hfn_eq in Hb_open |- *.
          rewrite <- Hkeeps. exact Hb_open. }
        (* ~ is_root e_ctx (atom_ret b): by roots_mono contrap *)
        assert (Hnr_ctx : ~ Semantics.is_root V V V_map V_map V_trie X e_ctx (atom_ret b)).
        { intro Hr_ctx. apply Hnr_open. exact (Hroots_mono (atom_ret b) Hr_ctx). }
        exact (Hcov b Hb_ctx Hnr_ctx). }
    Qed.

    (* [_gen] port: identical proof, over the [add_ctx_gen ... no_sort]
       context egraph.  The [add_open_*] frame lemmas are abstract over
       [sub] (need only [map fst sub = map fst c], supplied by
       [add_ctx_good_worklist_vc_gen]), so only the [add_ctx]→[add_ctx_gen]
       calls and the [sub]/[e_ctx] definitions change. *)
    Lemma good_worklist_eq_assum_gen (no_sort : V -> bool) c e1 t
        (Hwfc : wf_ctx l c) (Hwfe1 : wf_term l c e1 t)
      : exists ed_list,
          good_worklist V V V_map V_map V_trie X
            (snd (add_open_term succ sort_of l false false
                    (fst (add_ctx_gen succ sort_of l false false no_sort c (empty_egraph V_default X)))
                    e1
                    (snd (add_ctx_gen succ sort_of l false false no_sort c (empty_egraph V_default X)))))
            ed_list.
    Proof.
      pose proof (add_ctx_good_worklist_vc_gen no_sort c Hwfc) as Hvc.
      unfold vc in Hvc.
      set (e0 := @empty_egraph V V_default V V_map V_map V_trie X) in *.
      specialize (Hvc e0).
      assert (Huf0 : exists roots, union_find_ok lt (Defs.equiv e0) roots).
      { exact (ex_intro _ [] (@union_find_empty_ok V lt succ V_default V_map V_map_ok)). }
      assert (Hdb0 : @db_inv V V V_map V_map V_trie X (fun _ => True) e0).
      { intros aa Hin. exfalso. unfold Semantics.atom_in_db in Hin.
        unfold e0 in Hin. cbn [Defs.db empty_egraph] in Hin.
        rewrite map.get_empty in Hin. exact Hin. }
      assert (Hok0 : egraph_ok V lt V V_map V_map V_trie X e0).
      { exact (proj1 (@empty_sound_for_interpretation V lt succ V_default V V_map V_map_ok
                        V_map V_map_ok V_trie X lang_model)). }
      assert (Hpke0 : parents_keys_in_equiv V V V_map V_map V_trie X e0).
      { intros y [s Hs]. unfold e0 in Hs. cbn [parents empty_egraph] in Hs.
        rewrite map.get_empty in Hs. discriminate. }
      assert (Hac0 : SemanticsAnalysesCover.analyses_cover V V V_map V_map V_trie X e0).
      { intros z Hz. exfalso. unfold Sep.has_key in Hz. unfold e0 in Hz.
        cbn [equiv empty_egraph UnionFind.parent UnionFind.empty] in Hz.
        rewrite map.get_empty in Hz. exact Hz. }
      assert (Hwl0 : Defs.worklist e0 = []).
      { reflexivity. }
      specialize (Hvc Huf0 Hdb0 Hok0 Hpke0 Hac0 Hwl0).
      destruct Hvc as (Huf1 & Hdb1 & Hroots1 & Hmapfst & Hok1 & Hpke1 & Hac1 & [ed_list Hgw]).
      set (sub := fst (add_ctx_gen succ sort_of l false false no_sort c e0)) in *.
      set (e_ctx := snd (add_ctx_gen succ sort_of l false false no_sort c e0)) in *.
      set (e_open := snd (add_open_term succ sort_of l false false sub e1 e_ctx)).
      exists ed_list.
      unfold good_worklist in Hgw.
      destruct Hgw as (Hwl_eq & Hnodup & Hall_good & Hdisj & Hdbfalse & Hcov).
      assert (Hmapfst' : map fst c = map fst sub) by (symmetry; exact Hmapfst).
      pose proof (@Theorems.add_open_term_all_roots V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                    c sub e1 t Hwfe1 Hwfc Hmapfst') as Hroots.
      unfold vc in Hroots. specialize (Hroots e_ctx).
      fold e_open in Hroots.
      unfold Theorems.open_roots_post in Hroots.
      specialize (Hroots Huf1 Hdb1 Hroots1).
      fold e_open in Hroots.
      destruct Hroots as (Henv & _).
      unfold Theorems.roots_env in Henv.
      destruct Henv as (Huf_open & Hdb_open_ctx & Hdb_incl & Hroots_mono).
      assert (Hbase_keys : all (fun p => Sep.has_key (snd p) (parent (Defs.equiv e_ctx))) sub).
      { eapply all_wkn; [| exact Hroots1].
        intros p _ Hp. apply (Theorems.is_root_has_key V V_map V_trie X e_ctx (snd p)). exact Hp. }
      pose proof (@Theorems.add_open_worklist_frame V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf
                    l (add_open_sort succ sort_of l false false) Hwf (incl_refl l)
                    c Hwfc) as Hwlf.
      pose proof (proj1 Hwlf e1 t Hwfe1 sub Hmapfst') as Hwlf_term.
      unfold vc in Hwlf_term. specialize (Hwlf_term e_ctx).
      unfold Theorems.open_wlframe_post in Hwlf_term.
      specialize (Hwlf_term Hok1 Hac1 Hbase_keys).
      fold e_open in Hwlf_term.
      destruct Hwlf_term as (Hwl_open & Hok_open & _ & Hmono_key & _).
      unfold add_open_term in e_open.
      fold e_open in Hwl_open.
      fold e_open in Hok_open.
      fold e_open in Hmono_key.
      pose proof (@Theorems.add_open_node_atoms V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                    l (add_open_sort succ sort_of l false false) Hwf (incl_refl l)
                    c Hwfc) as Hnodes.
      pose proof (proj1 Hnodes e1 t Hwfe1 sub Hmapfst') as Hnode_term.
      unfold vc in Hnode_term. specialize (Hnode_term e_ctx).
      unfold Theorems.open_atomtree_post in Hnode_term.
      specialize (Hnode_term Huf1 Hdb1 Hroots1).
      cbn [fst snd] in Hnode_term.
      fold e_open in Hnode_term.
      destruct Hnode_term as (_ & _ & _ & Hext).
      pose proof (@Theorems.add_open_parents_frame V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                    l (add_open_sort succ sort_of l false false) Hwf (incl_refl l)
                    c Hwfc) as Hpf.
      pose proof (proj1 Hpf e1 t Hwfe1 sub Hmapfst') as Hpf_term.
      unfold vc in Hpf_term. specialize (Hpf_term e_ctx).
      fold e_open in Hpf_term.
      unfold Theorems.open_parents_frame_post in Hpf_term.
      fold e_open in Hpf_term.
      specialize (Hpf_term Hok1 Huf1 Hdb1 Hroots1).
      unfold good_worklist.
      split.
      { rewrite Hwl_open. exact Hwl_eq. }
      split.
      { exact Hnodup. }
      split.
      { apply all_via_in_local. intros d Hd_in.
        pose proof (in_all _ _ _ Hall_good Hd_in) as Hgd.
        unfold good_ed in Hgd |- *.
        destruct Hgd as (Hpar_d & Hatom_d & Hargs_d & Hret_d & Hnew_d & Hne_d & Huf_d).
        assert (Hhk_old : Sep.has_key (ed_old V V d) (parent (Defs.equiv e_ctx))).
        { apply Hpke1. exists [ed_atom V V d]. exact Hpar_d. }
        assert (Hnew_open : map.get (parent (Defs.equiv e_open)) (ed_new V V d) = Some (ed_new V V d)).
        { exact (Hroots_mono (ed_new V V d) Hnew_d). }
        assert (Huf_open_d : uf_rel_PER V (V_map V) (V_map nat) (Defs.equiv e_open) (ed_old V V d) (ed_new V V d)).
        { exact (Hext (ed_old V V d) (ed_new V V d) Huf_d). }
        assert (Hnr_old_open : ~ Semantics.is_root V V V_map V_map V_trie X e_open (ed_old V V d)).
        { intro Hroot_old.
          destruct Huf_open as [roots_open Hroots_open].
          exact (Hne_d (@Semantics.roots_uf_rel_eq V V_Eqb V_Eqb_ok lt V_default V_map V_map_ok
                          (Defs.equiv e_open) roots_open (ed_old V V d) (ed_new V V d) Hroots_open
                          Hroot_old Hnew_open Huf_open_d)). }
        split.
        { rewrite (Hpf_term (ed_old V V d) Hhk_old Hnr_old_open). exact Hpar_d. }
        split. { exact (Hdb_incl (ed_atom V V d) Hatom_d). }
        split. { eapply all_wkn; [| exact Hargs_d]. intros z _ Hz. exact (Hroots_mono z Hz). }
        split. { exact Hret_d. }
        split. { exact Hnew_open. }
        split. { exact Hne_d. }
        { exact Huf_open_d. } }
      split.
      { exact Hdisj. }
      split.
      { unfold db_inv. intros a Ha.
        destruct (Hdb_open_ctx a Ha) as [Hargs_roots _].
        split; [exact Hargs_roots | intro HF; destruct HF]. }
      { intros b Hb_open Hnr_open.
        assert (Hfn_eq : atom_fn b = sort_of).
        { destruct (Hdb_open_ctx b Hb_open) as [_ Hret_root].
          pose proof (V_Eqb_ok (atom_fn b) sort_of) as Heqb_case.
          destruct (eqb (atom_fn b) sort_of) eqn:Heqb.
          - exact Heqb_case.
          - exfalso. apply Hnr_open. exact (Hret_root Heqb_case). }
        assert (Hb_ctx : atom_in_db V V V_map V_trie X b (Defs.db e_ctx)).
        { pose proof (@Theorems.add_open_term'_keeps_sortof V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                        V_trie succ sort_of lt X HX l Hsof
                        (add_open_sort succ sort_of l false false)
                        (fun sub0 t0 e => @Theorems.add_open_sort'_keeps_sortof V V_Eqb V_Eqb_ok V_default
                                           V_map V_map_ok V_trie succ sort_of lt X HX l Hsof
                                           (S (length l)) sub0 t0 e)
                        sub e1 e_ctx) as Hkeeps.
          unfold Semantics.atom_in_db, Is_Some_satisfying in Hb_open |- *.
          rewrite Hfn_eq in Hb_open |- *.
          rewrite <- Hkeeps. exact Hb_open. }
        assert (Hnr_ctx : ~ Semantics.is_root V V V_map V_map V_trie X e_ctx (atom_ret b)).
        { intro Hr_ctx. apply Hnr_open. exact (Hroots_mono (atom_ret b) Hr_ctx). }
        exact (Hcov b Hb_ctx Hnr_ctx). }
    Qed.

    Lemma eq_ctx_inversion (rf : nat) (a : interp) c e1 t
        (Hwfc : wf_ctx l c) (Hwfe1 : wf_term l c e1 t)
      : fst (rebuild rf (snd (add_open_term succ sort_of l false false
                (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                e1
                (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))))
          = Result.Success tt ->
        (forall al, @Semantics.atom_in_egraph V V V_map V_map V_trie X al
                (snd (rebuild rf (snd (add_open_term succ sort_of l false false
                  (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                  e1
                  (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))))
              -> @Semantics.atom_sound_for_model V V V_map lang_model a al) ->
        exists sg, wf_subst l [] sg c
                /\ map fst sg = map fst c
                /\ (forall x, In x (map fst (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))) ->
                      map.get a (named_list_lookup default
                                  (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))) x)
                        = Some (inl (named_list_lookup default sg x))).
    Proof.
      intros Hsucc Hsound.
      change (empty_egraph V_default X)
        with (@empty_egraph V V_default V V_map V_map V_trie X) in *.
      set (e0 := @empty_egraph V V_default V V_map V_map V_trie X) in *.
      set (sub := fst (add_ctx succ sort_of l false false c e0)) in *.
      set (e_ctx := snd (add_ctx succ sort_of l false false c e0)) in *.
      set (e_open := snd (add_open_term succ sort_of l false false sub e1 e_ctx)) in *.
      set (eF := snd (rebuild rf e_open)) in *.
      (* --- base facts at empty_egraph --- *)
      assert (Hok0 : egraph_ok V lt V V_map V_map V_trie X e0)
        by exact (proj1 (@empty_sound_for_interpretation V lt succ V_default V V_map V_map_ok
                           V_map V_map_ok V_trie X lang_model)).
      assert (Huf0 : exists roots, union_find_ok lt (Defs.equiv e0) roots)
        by exact (ex_intro _ [] (@union_find_empty_ok V lt succ V_default V_map V_map_ok)).
      assert (Hdb0 : db_ctx_inv V V_map V_trie sort_of X e0)
        by (intros aa Hin; exfalso;
            unfold Semantics.atom_in_db in Hin;
            unfold e0 in Hin; cbn [Defs.db empty_egraph] in Hin;
            rewrite map.get_empty in Hin; exact Hin).
      (* --- add_ctx_egraph_ok: structural envelope --- *)
      pose proof (@Theorems.add_ctx_egraph_ok V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as HE.
      unfold vc in HE. specialize (HE e0).
      fold sub e_ctx in HE.
      specialize (HE Huf0 Hdb0 Hok0).
      destruct HE as (Huf1 & Hdb1 & Hroots1 & Hmapfst & Hok1).
      (* --- add_ctx_readback: model-free per-var readback --- *)
      pose proof (@Theorems.add_ctx_readback V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as HR.
      unfold vc in HR. specialize (HR e0).
      fold sub e_ctx in HR.
      specialize (HR Huf0 Hdb0).
      destruct HR as (_ & _ & _ & _ & Hrb).
      (* --- source e_open facts from add_open_term_all_roots --- *)
      assert (Hmapfst' : map fst c = map fst sub) by (symmetry; exact Hmapfst).
      pose proof (@Theorems.add_open_term_all_roots V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                    c sub e1 t Hwfe1 Hwfc Hmapfst') as Hroots.
      unfold vc in Hroots. specialize (Hroots e_ctx).
      fold e_open in Hroots.
      unfold Theorems.open_roots_post in Hroots.
      specialize (Hroots Huf1 Hdb1 Hroots1).
      fold e_open in Hroots.
      destruct Hroots as (Henv & _).
      unfold Theorems.roots_env in Henv.
      destruct Henv as (Huf_open & Hdb_open & Hdb_incl & Hroots_mono).
      (* --- egraph_ok e_open from add_open_worklist_frame --- *)
      assert (Hbase_keys : all (fun p => Sep.has_key (snd p) (parent (Defs.equiv e_ctx))) sub)
        by (eapply all_wkn; [| exact Hroots1];
            intros p _ Hp; apply (Theorems.is_root_has_key V V_map V_trie X e_ctx (snd p)); exact Hp).
      (* We need analyses_cover for e_ctx; get it from add_ctx_good_worklist_vc *)
      pose proof (add_ctx_good_worklist_vc c Hwfc) as Hvc_full.
      unfold vc in Hvc_full. specialize (Hvc_full e0).
      assert (Hpke0 : parents_keys_in_equiv V V V_map V_map V_trie X e0)
        by (intros y [s Hs]; unfold e0 in Hs; cbn [parents empty_egraph] in Hs;
            rewrite map.get_empty in Hs; discriminate).
      assert (Hac0 : SemanticsAnalysesCover.analyses_cover V V V_map V_map V_trie X e0)
        by (intros z Hz; exfalso; unfold Sep.has_key in Hz; unfold e0 in Hz;
            cbn [equiv empty_egraph UnionFind.parent UnionFind.empty] in Hz;
            rewrite map.get_empty in Hz; exact Hz).
      assert (Hwl0 : Defs.worklist e0 = []) by reflexivity.
      specialize (Hvc_full Huf0
                           (fun aa Hin => ltac:(exfalso; unfold Semantics.atom_in_db in Hin;
                                                unfold e0 in Hin; cbn [Defs.db empty_egraph] in Hin;
                                                rewrite map.get_empty in Hin; exact Hin))
                           Hok0 Hpke0 Hac0 Hwl0).
      destruct Hvc_full as (_ & _ & _ & _ & _ & _ & Hac1 & _).
      fold sub e_ctx in Hac1.
      pose proof (@Theorems.add_open_worklist_frame V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf
                    l (add_open_sort succ sort_of l false false) Hwf (incl_refl l)
                    c Hwfc) as Hwlf.
      pose proof (proj1 Hwlf e1 t Hwfe1 sub Hmapfst') as Hwlf_term.
      unfold vc in Hwlf_term. specialize (Hwlf_term e_ctx).
      unfold Theorems.open_wlframe_post in Hwlf_term.
      specialize (Hwlf_term Hok1 Hac1 Hbase_keys).
      fold e_open in Hwlf_term.
      destruct Hwlf_term as (_ & Hok_open & _ & _ & _).
      unfold add_open_term in e_open.
      fold e_open in Hok_open.
      (* --- equiv_extends e_ctx e_open from add_open_node_atoms --- *)
      pose proof (@Theorems.add_open_node_atoms V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                    l (add_open_sort succ sort_of l false false) Hwf (incl_refl l)
                    c Hwfc) as Hnodes.
      pose proof (proj1 Hnodes e1 t Hwfe1 sub Hmapfst') as Hnode_term.
      unfold vc in Hnode_term. specialize (Hnode_term e_ctx).
      unfold Theorems.open_atomtree_post in Hnode_term.
      specialize (Hnode_term Huf1 Hdb1 Hroots1).
      cbn [fst snd] in Hnode_term.
      fold e_open in Hnode_term.
      destruct Hnode_term as (_ & _ & _ & Hext).
      (* --- lift ctx_readback from e_ctx to e_open via ctx_readback_mono --- *)
      pose proof (@Theorems.ctx_readback_mono V V_Eqb V_default V_map V_trie sort_of X
                    e_ctx e_open sub c Hdb_incl Hroots_mono Hext Hrb) as Hrb_open.
      (* --- Hroots_open: sub roots in e_open --- *)
      assert (Hroots_open : all (fun p => is_root V V_map V_trie X e_open (snd p)) sub)
        by (eapply all_wkn; [| exact Hroots1];
            intros p _ Hp; exact (Hroots_mono (snd p) Hp)).
      (* --- good_worklist e_open from good_worklist_eq_assum --- *)
      pose proof (good_worklist_eq_assum c e1 t Hwfc Hwfe1) as Hgwl_open.
      unfold add_open_term in Hgwl_open.
      fold e0 sub e_ctx e_open in Hgwl_open.
      (* --- rebuild_survives_canonical for e_open --- *)
      pose proof (@rebuild_survives_canonical V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt X HX l Hwf Hsof
                    e_open rf Hok_open Hgwl_open Hsucc) as Hsurv.
      (* --- ctx_readback_to_eF for e_open --- *)
      pose proof (@CtxReadback.ctx_readback_to_eF V V_Eqb V_default V_map V_trie sort_of X l Hsof
                    e_open eF Hdb_open Hsurv c sub Hwfc Hroots_open Hrb_open) as Hrbef.
      (* --- ctx_readback_wf_subst: finish --- *)
      exact (@CtxReadback.ctx_readback_wf_subst V V_Eqb V_Eqb_ok V_default V_map V_trie sort_of X l Hwf Hsof
               eF a Hsound c sub Hwfc (eq_sym Hmapfst) Hrbef).
    Qed.

    (* ============================================================ *)
    (* MINIMIZED-QUERY substitution inversion (the SINGLE confined    *)
    (* admit for the skip-sorts feature).                             *)
    (*                                                                *)
    (* Same conclusion as [eq_ctx_inversion] but over the minimized   *)
    (* context egraph [add_ctx_gen ... no_sort c]: context variables  *)
    (* [x] with [no_sort x = true] carry NO [sort_of] atom (their     *)
    (* sort requirement is dropped from the query).  [Hskip] records  *)
    (* the soundness side condition the caller establishes: a skipped  *)
    (* var occurs in the LHS [e1], so its node is bound by the LHS     *)
    (* atoms.                                                          *)
    (*                                                                 *)
    (* WHY ADMITTED: recovering [wf_subst l [] sg c] needs each var    *)
    (* well-formed at its DECLARED (substituted) sort.  Skipped vars   *)
    (* have no [sort_of] atom, so their declared-sort wf must come     *)
    (* from the LHS image; but the e-graph model interprets atoms only *)
    (* up to [eq_term]/[eq_sort] (see [lang_model_interprets_to]:      *)
    (* [interprets_to_term] yields an output merely [eq_term] to       *)
    (* [con f args], never syntactically equal), so the syntactic      *)
    (* image needed by [Core.wf_subst_from_image] / the declared-sort  *)
    (* conversion both route through [add_open_faithful_rep], which     *)
    (* itself needs [wf_subst].  Closing this is the research-grade    *)
    (* "minimized substitution inversion": a simultaneous wf_subst +   *)
    (* per-var covering by a well-founded order over the ctx-telescope  *)
    (* and the LHS argument order.  The value map + leaf               *)
    (* correspondence ([CtxReadback.ctx_readback_vals_gen]) and the    *)
    (* covering entry points ([Core.wf_subst_from_image]) are proved;  *)
    (* the combined construction is the gap.  See memory               *)
    (* min_sorts_query for the full analysis. *)
    Lemma eq_ctx_inversion_gen (no_sort : V -> bool) (rf : nat) (a : interp) c e1 t
        (Hwfc : wf_ctx l c) (Hwfe1 : wf_term l c e1 t)
        (Hskip : forall x, no_sort x = true -> In x (fv e1))
      : fst (rebuild rf (snd (add_open_term succ sort_of l false false
                (fst (add_ctx_gen succ sort_of l false false no_sort c (empty_egraph V_default X)))
                e1
                (snd (add_ctx_gen succ sort_of l false false no_sort c (empty_egraph V_default X))))))
          = Result.Success tt ->
        (forall al, @Semantics.atom_in_egraph V V V_map V_map V_trie X al
                (snd (rebuild rf (snd (add_open_term succ sort_of l false false
                  (fst (add_ctx_gen succ sort_of l false false no_sort c (empty_egraph V_default X)))
                  e1
                  (snd (add_ctx_gen succ sort_of l false false no_sort c (empty_egraph V_default X)))))))
              -> @Semantics.atom_sound_for_model V V V_map lang_model a al) ->
        exists sg, wf_subst l [] sg c
                /\ map fst sg = map fst c
                /\ (forall x, In x (map fst (fst (add_ctx_gen succ sort_of l false false no_sort c (empty_egraph V_default X)))) ->
                      map.get a (named_list_lookup default
                                  (fst (add_ctx_gen succ sort_of l false false no_sort c (empty_egraph V_default X))) x)
                        = Some (inl (named_list_lookup default sg x))).
    Proof.
    Admitted.

    Lemma eq_assumption_inversion (rf : nat) (a : interp) c e1 t
        (Hwfc : wf_ctx l c) (Hwfe1 : wf_term l c e1 t)
        (Hsucc : fst (rebuild rf (snd (add_open_term succ sort_of l false false
                  (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                  e1
                  (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))))
            = Result.Success tt)
        (Hsound : forall al, @Semantics.atom_in_egraph V V V_map V_map V_trie X al
                (snd (rebuild rf (snd (add_open_term succ sort_of l false false
                  (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                  e1
                  (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))))
              -> @Semantics.atom_sound_for_model V V V_map lang_model a al)
      : exists sg, wf_subst l [] sg c
              /\ map fst sg = map fst c
              /\ (forall x, In x (map fst (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))) ->
                    map.get a (named_list_lookup default
                                (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))) x)
                      = Some (inl (named_list_lookup default sg x)))
              /\ (exists e1',
                    map.get a (fst (add_open_term succ sort_of l false false
                                (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                                e1
                                (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))
                      = Some (inl e1')
                    /\ eq_term l [] t[/sg/] e1' e1[/sg/]).
    Proof.
      (* Step 1: get sg from eq_ctx_inversion *)
      pose proof (eq_ctx_inversion rf a c e1 t Hwfc Hwfe1 Hsucc Hsound)
        as (sg & Hsg & Hmapfst & Hfaith).
      (* set up abbreviations *)
      change (empty_egraph V_default X)
        with (@empty_egraph V V_default V V_map V_map V_trie X) in *.
      set (e0 := @empty_egraph V V_default V V_map V_map V_trie X) in *.
      set (sub := fst (add_ctx succ sort_of l false false c e0)) in *.
      set (e_ctx := snd (add_ctx succ sort_of l false false c e0)) in *.
      set (e_open := snd (add_open_term succ sort_of l false false sub e1 e_ctx)) in *.
      set (x1 := fst (add_open_term succ sort_of l false false sub e1 e_ctx)) in *.
      set (eF := snd (rebuild rf e_open)) in *.
      (* Step 2: base facts at empty_egraph *)
      assert (Hok0 : egraph_ok V lt V V_map V_map V_trie X e0)
        by exact (proj1 (@empty_sound_for_interpretation V lt succ V_default V V_map V_map_ok
                           V_map V_map_ok V_trie X lang_model)).
      assert (Huf0 : exists roots, union_find_ok lt (Defs.equiv e0) roots)
        by exact (ex_intro _ [] (@union_find_empty_ok V lt succ V_default V_map V_map_ok)).
      assert (Hdb0 : db_ctx_inv V V_map V_trie sort_of X e0)
        by (intros aa Hin; exfalso;
            unfold Semantics.atom_in_db in Hin;
            unfold e0 in Hin; cbn [Defs.db empty_egraph] in Hin;
            rewrite map.get_empty in Hin; exact Hin).
      (* Step 3: add_ctx_egraph_ok *)
      pose proof (@Theorems.add_ctx_egraph_ok V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as HE.
      unfold vc in HE. specialize (HE e0).
      fold sub e_ctx in HE.
      specialize (HE Huf0 Hdb0 Hok0).
      destruct HE as (Huf1 & Hdb1 & Hroots1 & Hmapfst_sub & Hok1).
      assert (Hmapfst' : map fst c = map fst sub) by (symmetry; exact Hmapfst_sub).
      fold sub e_ctx in Huf1, Hdb1, Hroots1, Hmapfst_sub, Hok1.
      (* Step 4: add_open_node_atoms -> atom_tree X e_open sub e1 x1 *)
      pose proof (@Theorems.add_open_node_atoms V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                    l (add_open_sort succ sort_of l false false) Hwf (incl_refl l)
                    c Hwfc) as Hnodes.
      pose proof (proj1 Hnodes e1 t Hwfe1 sub Hmapfst') as Hnode_term.
      unfold vc in Hnode_term. specialize (Hnode_term e_ctx).
      unfold Theorems.open_atomtree_post in Hnode_term.
      specialize (Hnode_term Huf1 Hdb1 Hroots1).
      cbn [fst snd] in Hnode_term.
      fold e_open x1 in Hnode_term.
      destruct Hnode_term as (Henv_open & Hx1_root & Htree_open & _).
      unfold Theorems.roots_env in Henv_open.
      destruct Henv_open as (Huf_open & Hdb_open & Hdb_incl & Hroots_mono).
      (* unfold add_open_term to match e_open/x1 definitions *)
      unfold add_open_term in e_open, x1.
      fold e_open x1 in Huf_open, Hdb_open, Hdb_incl, Hroots_mono, Hx1_root, Htree_open.
      (* Step 5: egraph_ok e_open from add_open_worklist_frame *)
      assert (Hbase_keys : all (fun p => Sep.has_key (snd p) (parent (Defs.equiv e_ctx))) sub)
        by (eapply all_wkn; [| exact Hroots1];
            intros p _ Hp; apply (Theorems.is_root_has_key V V_map V_trie X e_ctx (snd p)); exact Hp).
      pose proof (add_ctx_good_worklist_vc c Hwfc) as Hvc_full.
      unfold vc in Hvc_full. specialize (Hvc_full e0).
      assert (Hpke0 : parents_keys_in_equiv V V V_map V_map V_trie X e0)
        by (intros y [s Hs]; unfold e0 in Hs; cbn [parents empty_egraph] in Hs;
            rewrite map.get_empty in Hs; discriminate).
      assert (Hac0 : SemanticsAnalysesCover.analyses_cover V V V_map V_map V_trie X e0)
        by (intros z Hz; exfalso; unfold Sep.has_key in Hz; unfold e0 in Hz;
            cbn [equiv empty_egraph UnionFind.parent UnionFind.empty] in Hz;
            rewrite map.get_empty in Hz; exact Hz).
      assert (Hwl0 : Defs.worklist e0 = []) by reflexivity.
      specialize (Hvc_full Huf0
                           (fun aa Hin => ltac:(exfalso; unfold Semantics.atom_in_db in Hin;
                                                unfold e0 in Hin; cbn [Defs.db empty_egraph] in Hin;
                                                rewrite map.get_empty in Hin; exact Hin))
                           Hok0 Hpke0 Hac0 Hwl0).
      destruct Hvc_full as (_ & _ & _ & _ & _ & _ & Hac1 & _).
      fold sub e_ctx in Hac1.
      pose proof (@Theorems.add_open_worklist_frame V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf
                    l (add_open_sort succ sort_of l false false) Hwf (incl_refl l)
                    c Hwfc) as Hwlf.
      pose proof (proj1 Hwlf e1 t Hwfe1 sub Hmapfst') as Hwlf_term.
      unfold vc in Hwlf_term. specialize (Hwlf_term e_ctx).
      unfold Theorems.open_wlframe_post in Hwlf_term.
      specialize (Hwlf_term Hok1 Hac1 Hbase_keys).
      fold e_open in Hwlf_term.
      destruct Hwlf_term as (_ & Hok_open & _ & _ & _).
      unfold add_open_term in e_open.
      fold e_open in Hok_open.
      (* Step 6: good_worklist e_open *)
      pose proof (good_worklist_eq_assum c e1 t Hwfc Hwfe1) as Hgwl_open.
      unfold add_open_term in Hgwl_open.
      fold e0 sub e_ctx e_open in Hgwl_open.
      (* Step 7: rebuild_survives_canonical for e_open *)
      pose proof (@rebuild_survives_canonical V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt X HX l Hwf Hsof
                    e_open rf Hok_open Hgwl_open Hsucc) as Hsurv0.
      fold eF in Hsurv0.
      (* Step 8: build Hsurv : atom_in_egraph a0 e_open -> roots -> atom_in_egraph a0 eF
         by bridging atom_in_egraph -> atom_in_egraph_up_to_equiv via reflexivity *)
      assert (Hrefl_per : forall xl,
                 all (is_root V V_map V_trie X e_open) xl ->
                 all2 (UnionFind.uf_rel_PER V (V_map V) (V_map nat) (Defs.equiv e_open)) xl xl)
        by (induction xl as [|z xl IHxl]; cbn; [trivial|];
            intros [Hz Hxl]; split;
            [apply Relations.PER_clo_base; exact Hz | apply IHxl; exact Hxl]).
      assert (Hsurv : forall a0 : atom,
                 @Semantics.atom_in_egraph V V V_map V_map V_trie X a0 e_open ->
                 all (is_root V V_map V_trie X e_open) (atom_args a0) ->
                 is_root V V_map V_trie X e_open (atom_ret a0) ->
                 @Semantics.atom_in_egraph V V V_map V_map V_trie X a0 eF)
        by (intros a0 Ha0_in Ha0_args Ha0_ret;
            apply Hsurv0; [ | exact Ha0_args | exact Ha0_ret ];
            exists a0; split; [| exact Ha0_in];
            unfold Semantics.atom_canonical_equiv; split; [reflexivity|]; split;
            [apply Hrefl_per; exact Ha0_args | apply Relations.PER_clo_base; exact Ha0_ret]).
      (* Step 9: atom_tree X eF sub e1 x1 *)
      pose proof (@Theorems.atom_tree_survives V V_Eqb V_default V_map V_trie sort_of X l Hsof
                    e_open eF sub c Hdb_open Hsurv e1 t Hwfe1 x1 Htree_open) as Htree_eF.
      (* Step 10: represents a eF sg e1 x1 *)
      pose proof (@Theorems.atom_tree_to_represents V V_Eqb V_Eqb_ok V_default V_map V_trie sort_of X l Hwf
                    a eF sub sg c Hfaith (eq_sym Hmapfst_sub) e1 t Hwfe1 x1 Htree_eF) as Hrep.
      (* Step 11: add_open_faithful_rep -> exists e1' *)
      pose proof (@Theorems.add_open_faithful_rep V V_Eqb V_Eqb_ok V_default V_map V_trie sort_of X l Hwf Hsof
                    a eF sg c Hwfc Hsound Hsg e1 t Hwfe1 x1 Hrep) as He1'.
      (* Assemble the conclusion *)
      exact (ex_intro _ sg (conj Hsg (conj Hmapfst (conj Hfaith He1')))).
    Qed.

    (* ============================================================ *)
    (* Frame lemmas for the COMBINED eq-assumption egraph             *)
    (*   e_open = add_open_term false false sub e1 (add_ctx c);        *)
    (*   eF     = rebuild rf e_open.                                   *)
    (* These mirror [assum_sortof_frame_eF] / [assum_db_frame_eF]      *)
    (* (the add_ctx-only versions in Section F1cDischarge) but the     *)
    (* PRE egraph is [e_open], which carries e1's term atoms in        *)
    (* addition to the ctx-var atoms.  add_open (false false) adds NO  *)
    (* sort_of atoms, so the sort_of frame is unchanged; the non-      *)
    (* sort_of frame gains an "e1-tree node" disjunct.                 *)
    (* The whole e_open->eF survival scaffolding (Hok_open,            *)
    (* good_worklist e_open, Hsurv, atom_tree eF sub e1 x1) is exactly *)
    (* the preamble of [eq_assumption_inversion] (Steps 2-9).          *)
    (* ============================================================ *)

    Lemma eq_assum_sortof_frame_eF (rf : nat) c e1 t
      (Hwfc : wf_ctx l c) (Hwfe1 : wf_term l c e1 t)
      (Hsucc : fst (rebuild rf (snd (add_open_term succ sort_of l false false
                (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                e1
                (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))))
               = Result.Success tt)
      : forall b,
          @Semantics.atom_in_egraph V V V_map V_map V_trie X b
            (snd (rebuild rf (snd (add_open_term succ sort_of l false false
                (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                e1
                (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))))) ->
          b.(atom_fn) = sort_of ->
          exists nm x', b.(atom_args) = [x'] /\
            In (nm, x') (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))).
    Proof.
      intros b Hb Hbfn.
      change (empty_egraph V_default X)
        with (@empty_egraph V V_default V V_map V_map V_trie X) in *.
      set (e0 := @empty_egraph V V_default V V_map V_map V_trie X) in *.
      set (sub := fst (add_ctx succ sort_of l false false c e0)) in *.
      set (e_ctx := snd (add_ctx succ sort_of l false false c e0)) in *.
      set (e_open := snd (add_open_term succ sort_of l false false sub e1 e_ctx)) in *.
      set (x1 := fst (add_open_term succ sort_of l false false sub e1 e_ctx)) in *.
      set (eF := snd (rebuild rf e_open)) in *.
      (* Step 2: base facts at empty_egraph *)
      assert (Hok0 : egraph_ok V lt V V_map V_map V_trie X e0)
        by exact (proj1 (@empty_sound_for_interpretation V lt succ V_default V V_map V_map_ok
                           V_map V_map_ok V_trie X lang_model)).
      assert (Huf0 : exists roots, union_find_ok lt (Defs.equiv e0) roots)
        by exact (ex_intro _ [] (@union_find_empty_ok V lt succ V_default V_map V_map_ok)).
      assert (Hdb0 : db_ctx_inv V V_map V_trie sort_of X e0)
        by (intros aa Hin; exfalso;
            unfold Semantics.atom_in_db in Hin;
            unfold e0 in Hin; cbn [Defs.db empty_egraph] in Hin;
            rewrite map.get_empty in Hin; exact Hin).
      (* Step 3: add_ctx_egraph_ok *)
      pose proof (@Theorems.add_ctx_egraph_ok V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as HE.
      unfold vc in HE. specialize (HE e0).
      fold sub e_ctx in HE.
      specialize (HE Huf0 Hdb0 Hok0).
      destruct HE as (Huf1 & Hdb1 & Hroots1 & Hmapfst_sub & Hok1).
      assert (Hmapfst' : map fst c = map fst sub) by (symmetry; exact Hmapfst_sub).
      fold sub e_ctx in Huf1, Hdb1, Hroots1, Hmapfst_sub, Hok1.
      (* Step 4: add_open_node_atoms -> e_open env facts *)
      pose proof (@Theorems.add_open_node_atoms V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                    l (add_open_sort succ sort_of l false false) Hwf (incl_refl l)
                    c Hwfc) as Hnodes.
      pose proof (proj1 Hnodes e1 t Hwfe1 sub Hmapfst') as Hnode_term.
      unfold vc in Hnode_term. specialize (Hnode_term e_ctx).
      unfold Theorems.open_atomtree_post in Hnode_term.
      specialize (Hnode_term Huf1 Hdb1 Hroots1).
      cbn [fst snd] in Hnode_term.
      fold e_open x1 in Hnode_term.
      destruct Hnode_term as (Henv_open & Hx1_root & Htree_open & _).
      unfold Theorems.roots_env in Henv_open.
      destruct Henv_open as (Huf_open & Hdb_open & Hdb_incl & Hroots_mono).
      unfold add_open_term in e_open, x1.
      fold e_open x1 in Huf_open, Hdb_open, Hdb_incl, Hroots_mono, Hx1_root, Htree_open.
      fold sub e_ctx in Huf1, Hdb1, Hroots1, Hmapfst_sub, Hok1.
      (* Step 5: egraph_ok e_open from add_open_worklist_frame *)
      assert (Hbase_keys : all (fun p => Sep.has_key (snd p) (parent (Defs.equiv e_ctx))) sub)
        by (eapply all_wkn; [| exact Hroots1];
            intros p _ Hp; apply (Theorems.is_root_has_key V V_map V_trie X e_ctx (snd p)); exact Hp).
      pose proof (add_ctx_good_worklist_vc c Hwfc) as Hvc_full.
      unfold vc in Hvc_full. specialize (Hvc_full e0).
      assert (Hpke0 : parents_keys_in_equiv V V V_map V_map V_trie X e0)
        by (intros y [s Hs]; unfold e0 in Hs; cbn [parents empty_egraph] in Hs;
            rewrite map.get_empty in Hs; discriminate).
      assert (Hac0 : SemanticsAnalysesCover.analyses_cover V V V_map V_map V_trie X e0)
        by (intros z Hz; exfalso; unfold Sep.has_key in Hz; unfold e0 in Hz;
            cbn [equiv empty_egraph UnionFind.parent UnionFind.empty] in Hz;
            rewrite map.get_empty in Hz; exact Hz).
      assert (Hwl0 : Defs.worklist e0 = []) by reflexivity.
      specialize (Hvc_full Huf0
                           (fun aa Hin => ltac:(exfalso; unfold Semantics.atom_in_db in Hin;
                                                unfold e0 in Hin; cbn [Defs.db empty_egraph] in Hin;
                                                rewrite map.get_empty in Hin; exact Hin))
                           Hok0 Hpke0 Hac0 Hwl0).
      destruct Hvc_full as (_ & _ & _ & _ & _ & _ & Hac1 & _).
      fold sub e_ctx in Hac1.
      pose proof (@Theorems.add_open_worklist_frame V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf
                    l (add_open_sort succ sort_of l false false) Hwf (incl_refl l)
                    c Hwfc) as Hwlf.
      pose proof (proj1 Hwlf e1 t Hwfe1 sub Hmapfst') as Hwlf_term.
      unfold vc in Hwlf_term. specialize (Hwlf_term e_ctx).
      unfold Theorems.open_wlframe_post in Hwlf_term.
      specialize (Hwlf_term Hok1 Hac1 Hbase_keys).
      fold e_open in Hwlf_term.
      destruct Hwlf_term as (_ & Hok_open & _ & _ & _).
      unfold add_open_term in e_open.
      fold e_open in Hok_open.
      (* Step 6: good_worklist e_open *)
      pose proof (good_worklist_eq_assum c e1 t Hwfc Hwfe1) as Hgwl_open.
      unfold add_open_term in Hgwl_open.
      fold e0 sub e_ctx e_open in Hgwl_open.
      (* Step 7: rebuild_survives_canonical for e_open *)
      pose proof (@rebuild_survives_canonical V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt X HX l Hwf Hsof
                    e_open rf Hok_open Hgwl_open Hsucc) as Hsurv0.
      fold eF in Hsurv0.
      (* Step 8: build Hsurv *)
      assert (Hrefl_per : forall xl,
                 all (is_root V V_map V_trie X e_open) xl ->
                 all2 (UnionFind.uf_rel_PER V (V_map V) (V_map nat) (Defs.equiv e_open)) xl xl)
        by (induction xl as [|z xl IHxl]; cbn; [trivial|];
            intros [Hz Hxl]; split;
            [apply Relations.PER_clo_base; exact Hz | apply IHxl; exact Hxl]).
      assert (Hsurv : forall a0 : atom,
                 @Semantics.atom_in_egraph V V V_map V_map V_trie X a0 e_open ->
                 all (is_root V V_map V_trie X e_open) (atom_args a0) ->
                 is_root V V_map V_trie X e_open (atom_ret a0) ->
                 @Semantics.atom_in_egraph V V V_map V_map V_trie X a0 eF)
        by (intros a0 Ha0_in Ha0_args Ha0_ret;
            apply Hsurv0; [ | exact Ha0_args | exact Ha0_ret ];
            exists a0; split; [| exact Ha0_in];
            unfold Semantics.atom_canonical_equiv; split; [reflexivity|]; split;
            [apply Hrefl_per; exact Ha0_args | apply Relations.PER_clo_base; exact Ha0_ret]).
      (* Step 9: atom_tree X eF sub e1 x1 *)
      pose proof (@Theorems.atom_tree_survives V V_Eqb V_default V_map V_trie sort_of X l Hsof
                    e_open eF sub c Hdb_open Hsurv e1 t Hwfe1 x1 Htree_open) as Htree_eF.
      (* rebuild_canon on e_open *)
      destruct rf as [|fuel]; [exfalso; cbn in Hsucc; discriminate Hsucc|].
      destruct Hgwl_open as [ed_list Hgwl_open].
      pose proof (@rebuild_canon V V_Eqb V_Eqb_ok lt succ V_default
                    V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                    X HX (Theorems.lang_model V sort_of l)
                    (@Theorems.lang_model_ok V V_Eqb V_Eqb_ok sort_of l Hsof Hwf)
                    fuel e_open ed_list Hok_open Hgwl_open) as (HdbT & Hmono & Hrev).
      destruct (Hrev b Hb) as (a & Ha_eopen_db & Hafn & Haargs).
      assert (Hafn_sof : atom_fn a = sort_of) by (rewrite Hafn; exact Hbfn).
      pose proof (@Theorems.add_open_term'_keeps_sortof V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie succ sort_of lt X HX l Hsof
                    (add_open_sort succ sort_of l false false)
                    (fun sub0 t0 e => @Theorems.add_open_sort'_keeps_sortof V V_Eqb V_Eqb_ok V_default
                                         V_map V_map_ok V_trie succ sort_of lt X HX l Hsof
                                         (S (length l)) sub0 t0 e)
                    sub e1 e_ctx) as Hkeeps.
      fold e_open in Hkeeps.
      assert (Ha_ectx_db : atom_in_db V V V_map V_trie X a (Defs.db e_ctx))
        by (unfold Semantics.atom_in_db in Ha_eopen_db |- *;
            rewrite Hafn_sof in Ha_eopen_db |- *;
            rewrite <- Hkeeps;
            exact Ha_eopen_db).
      pose proof (@Theorems.assum_sortof_frame_pre V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as Hsf_vc.
      unfold vc in Hsf_vc. specialize (Hsf_vc e0).
      fold sub e_ctx in Hsf_vc.
      assert (He0_nosof : forall a0, @Semantics.atom_in_egraph V V V_map V_map V_trie X a0 e0 -> a0.(atom_fn) <> sort_of)
        by (intros a0 Ha0; exfalso;
            unfold Semantics.atom_in_egraph, Semantics.atom_in_db in Ha0;
            unfold e0 in Ha0; cbn [Defs.db empty_egraph] in Ha0;
            rewrite map.get_empty in Ha0; exact Ha0).
      specialize (Hsf_vc Huf0 Hdb0 He0_nosof).
      destruct (Hsf_vc a Ha_ectx_db Hafn_sof) as (nm & x' & Hargs_a & Hin_sub).
      exists nm, x'. split; [ rewrite <- Haargs; exact Hargs_a | exact Hin_sub ].
    Qed.

    Lemma eq_assum_db_frame_eF (rf : nat) c e1 t
      (Hwfc : wf_ctx l c) (Hwfe1 : wf_term l c e1 t)
      (Hsucc : fst (rebuild rf (snd (add_open_term succ sort_of l false false
                (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                e1
                (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))))
               = Result.Success tt)
      : forall b,
          @Semantics.atom_in_egraph V V V_map V_map V_trie X b
            (snd (rebuild rf (snd (add_open_term succ sort_of l false false
                (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                e1
                (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))))) ->
          b.(atom_fn) <> sort_of ->
          (exists x n_x s_x xs_x,
            In (x, scon n_x s_x) c
            /\ atom_tree_sort V V_map V_trie X
                 (snd (rebuild rf (snd (add_open_term succ sort_of l false false
                   (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                   e1
                   (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))))
                 (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                 (scon n_x s_x) xs_x
            /\ atom_node V V_map V_trie X
                 (snd (rebuild rf (snd (add_open_term succ sort_of l false false
                   (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                   e1
                   (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))))
                 (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                 (con n_x s_x) xs_x b)
          \/ (exists xe,
                atom_tree V V_map V_trie X
                  (snd (rebuild rf (snd (add_open_term succ sort_of l false false
                    (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                    e1
                    (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))))
                  (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                  e1 xe
                /\ atom_node V V_map V_trie X
                     (snd (rebuild rf (snd (add_open_term succ sort_of l false false
                       (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                       e1
                       (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))))
                     (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                     e1 xe b).
    Proof.
      intros b Hb Hbfn.
      change (empty_egraph V_default X)
        with (@empty_egraph V V_default V V_map V_map V_trie X) in *.
      set (e0 := @empty_egraph V V_default V V_map V_map V_trie X) in *.
      set (sub := fst (add_ctx succ sort_of l false false c e0)) in *.
      set (e_ctx := snd (add_ctx succ sort_of l false false c e0)) in *.
      set (e_open := snd (add_open_term succ sort_of l false false sub e1 e_ctx)) in *.
      set (x1 := fst (add_open_term succ sort_of l false false sub e1 e_ctx)) in *.
      set (eF := snd (rebuild rf e_open)) in *.
      (* Step 2: base facts at empty_egraph *)
      assert (Hok0 : egraph_ok V lt V V_map V_map V_trie X e0)
        by exact (proj1 (@empty_sound_for_interpretation V lt succ V_default V V_map V_map_ok
                           V_map V_map_ok V_trie X lang_model)).
      assert (Huf0 : exists roots, union_find_ok lt (Defs.equiv e0) roots)
        by exact (ex_intro _ [] (@union_find_empty_ok V lt succ V_default V_map V_map_ok)).
      assert (Hdb0 : db_ctx_inv V V_map V_trie sort_of X e0)
        by (intros aa Hin; exfalso;
            unfold Semantics.atom_in_db in Hin;
            unfold e0 in Hin; cbn [Defs.db empty_egraph] in Hin;
            rewrite map.get_empty in Hin; exact Hin).
      (* Step 3: add_ctx_egraph_ok *)
      pose proof (@Theorems.add_ctx_egraph_ok V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as HE.
      unfold vc in HE. specialize (HE e0).
      fold sub e_ctx in HE.
      specialize (HE Huf0 Hdb0 Hok0).
      destruct HE as (Huf1 & Hdb1 & Hroots1 & Hmapfst_sub & Hok1).
      assert (Hmapfst' : map fst c = map fst sub) by (symmetry; exact Hmapfst_sub).
      fold sub e_ctx in Huf1, Hdb1, Hroots1, Hmapfst_sub, Hok1.
      (* Step 4: add_open_node_atoms -> e_open env facts *)
      pose proof (@Theorems.add_open_node_atoms V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                    l (add_open_sort succ sort_of l false false) Hwf (incl_refl l)
                    c Hwfc) as Hnodes.
      pose proof (proj1 Hnodes e1 t Hwfe1 sub Hmapfst') as Hnode_term.
      unfold vc in Hnode_term. specialize (Hnode_term e_ctx).
      unfold Theorems.open_atomtree_post in Hnode_term.
      specialize (Hnode_term Huf1 Hdb1 Hroots1).
      cbn [fst snd] in Hnode_term.
      fold e_open x1 in Hnode_term.
      destruct Hnode_term as (Henv_open & Hx1_root & Htree_open & _).
      unfold Theorems.roots_env in Henv_open.
      destruct Henv_open as (Huf_open & Hdb_open & Hdb_incl & Hroots_mono).
      unfold add_open_term in e_open, x1.
      fold e_open x1 in Huf_open, Hdb_open, Hdb_incl, Hroots_mono, Hx1_root, Htree_open.
      fold sub e_ctx in Huf1, Hdb1, Hroots1, Hmapfst_sub, Hok1.
      (* Step 5: egraph_ok e_open from add_open_worklist_frame *)
      assert (Hbase_keys : all (fun p => Sep.has_key (snd p) (parent (Defs.equiv e_ctx))) sub)
        by (eapply all_wkn; [| exact Hroots1];
            intros p _ Hp; apply (Theorems.is_root_has_key V V_map V_trie X e_ctx (snd p)); exact Hp).
      pose proof (add_ctx_good_worklist_vc c Hwfc) as Hvc_full.
      unfold vc in Hvc_full. specialize (Hvc_full e0).
      assert (Hpke0 : parents_keys_in_equiv V V V_map V_map V_trie X e0)
        by (intros y [s Hs]; unfold e0 in Hs; cbn [parents empty_egraph] in Hs;
            rewrite map.get_empty in Hs; discriminate).
      assert (Hac0 : SemanticsAnalysesCover.analyses_cover V V V_map V_map V_trie X e0)
        by (intros z Hz; exfalso; unfold Sep.has_key in Hz; unfold e0 in Hz;
            cbn [equiv empty_egraph UnionFind.parent UnionFind.empty] in Hz;
            rewrite map.get_empty in Hz; exact Hz).
      assert (Hwl0 : Defs.worklist e0 = []) by reflexivity.
      specialize (Hvc_full Huf0
                           (fun aa Hin => ltac:(exfalso; unfold Semantics.atom_in_db in Hin;
                                                unfold e0 in Hin; cbn [Defs.db empty_egraph] in Hin;
                                                rewrite map.get_empty in Hin; exact Hin))
                           Hok0 Hpke0 Hac0 Hwl0).
      destruct Hvc_full as (_ & _ & _ & _ & _ & _ & Hac1 & _).
      fold sub e_ctx in Hac1.
      pose proof (@Theorems.add_open_worklist_frame V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf
                    l (add_open_sort succ sort_of l false false) Hwf (incl_refl l)
                    c Hwfc) as Hwlf.
      pose proof (proj1 Hwlf e1 t Hwfe1 sub Hmapfst') as Hwlf_term.
      unfold vc in Hwlf_term. specialize (Hwlf_term e_ctx).
      unfold Theorems.open_wlframe_post in Hwlf_term.
      specialize (Hwlf_term Hok1 Hac1 Hbase_keys).
      fold e_open in Hwlf_term.
      destruct Hwlf_term as (_ & Hok_open & _ & _ & _).
      unfold add_open_term in e_open.
      fold e_open in Hok_open.
      (* Step 6: good_worklist e_open *)
      pose proof (good_worklist_eq_assum c e1 t Hwfc Hwfe1) as Hgwl_open.
      unfold add_open_term in Hgwl_open.
      fold e0 sub e_ctx e_open in Hgwl_open.
      (* Step 7: rebuild_survives_canonical for e_open *)
      pose proof (@rebuild_survives_canonical V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt X HX l Hwf Hsof
                    e_open rf Hok_open Hgwl_open Hsucc) as Hsurv0.
      fold eF in Hsurv0.
      (* Step 8: build Hsurv *)
      assert (Hrefl_per : forall xl,
                 all (is_root V V_map V_trie X e_open) xl ->
                 all2 (UnionFind.uf_rel_PER V (V_map V) (V_map nat) (Defs.equiv e_open)) xl xl)
        by (induction xl as [|z xl IHxl]; cbn; [trivial|];
            intros [Hz Hxl]; split;
            [apply Relations.PER_clo_base; exact Hz | apply IHxl; exact Hxl]).
      assert (Hsurv : forall a0 : atom,
                 @Semantics.atom_in_egraph V V V_map V_map V_trie X a0 e_open ->
                 all (is_root V V_map V_trie X e_open) (atom_args a0) ->
                 is_root V V_map V_trie X e_open (atom_ret a0) ->
                 @Semantics.atom_in_egraph V V V_map V_map V_trie X a0 eF)
        by (intros a0 Ha0_in Ha0_args Ha0_ret;
            apply Hsurv0; [ | exact Ha0_args | exact Ha0_ret ];
            exists a0; split; [| exact Ha0_in];
            unfold Semantics.atom_canonical_equiv; split; [reflexivity|]; split;
            [apply Hrefl_per; exact Ha0_args | apply Relations.PER_clo_base; exact Ha0_ret]).
      (* Step 9: atom_tree X eF sub e1 x1 *)
      pose proof (@Theorems.atom_tree_survives V V_Eqb V_default V_map V_trie sort_of X l Hsof
                    e_open eF sub c Hdb_open Hsurv e1 t Hwfe1 x1 Htree_open) as Htree_eF.
      (* Get Hnew_disj from add_open_new_atoms_are_nodes *)
      pose proof (@Theorems.add_open_new_atoms_are_nodes V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof l (add_open_sort succ sort_of l false false) Hwf (incl_refl l) c Hwfc) as Hnewat.
      pose proof (proj1 Hnewat e1 t Hwfe1 sub Hmapfst') as Hnewat_term.
      unfold vc in Hnewat_term. specialize (Hnewat_term e_ctx).
      unfold Theorems.open_newatom_post in Hnewat_term.
      specialize (Hnewat_term Huf1 Hdb1 Hroots1).
      cbn [fst snd] in Hnewat_term.
      fold e_open x1 in Hnewat_term.
      destruct Hnewat_term as (_ & _ & _ & _ & Hnew_disj).
      (* Build Hsurv_ctx: a0 ∈ e_ctx → (root conditions) → a0 ∈ eF *)
      assert (Hsurv_ctx : forall a0 : atom,
                 @Semantics.atom_in_egraph V V V_map V_map V_trie X a0 e_ctx ->
                 all (is_root V V_map V_trie X e_ctx) (atom_args a0) ->
                 is_root V V_map V_trie X e_ctx (atom_ret a0) ->
                 @Semantics.atom_in_egraph V V V_map V_map V_trie X a0 eF)
        by (intros a0 Ha0 Hargs Hret;
            apply Hsurv;
            [ exact (Hdb_incl a0 Ha0)
            | eapply all_wkn; [| exact Hargs]; intros z _ Hz; exact (Hroots_mono z Hz)
            | exact (Hroots_mono _ Hret) ]).
      (* rebuild_canon on e_open *)
      destruct rf as [|fuel]; [exfalso; cbn in Hsucc; discriminate Hsucc|].
      destruct Hgwl_open as [ed_list Hgwl_open].
      pose proof (@rebuild_canon V V_Eqb V_Eqb_ok lt succ V_default
                    V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                    X HX (Theorems.lang_model V sort_of l)
                    (@Theorems.lang_model_ok V V_Eqb V_Eqb_ok sort_of l Hsof Hwf)
                    fuel e_open ed_list Hok_open Hgwl_open) as (HdbT & Hmono & Hrev).
      destruct (Hrev b Hb) as (a & Ha_eopen_db & Hafn & Haargs).
      assert (Ha_eopen : @Semantics.atom_in_egraph V V V_map V_map V_trie X a e_open) by exact Ha_eopen_db.
      assert (Hafn_ne : atom_fn a <> sort_of) by (rewrite Hafn; exact Hbfn).
      destruct (Hnew_disj a Ha_eopen) as [Ha_ectx | Hnode_eopen].
      - (* LEFT BRANCH: a ∈ e_ctx *)
        pose proof (@Theorems.assum_db_frame_pre V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as Hframe_vc.
        unfold vc in Hframe_vc. specialize (Hframe_vc e0).
        fold sub e_ctx in Hframe_vc.
        assert (He0_sortof : forall a0, @Semantics.atom_in_egraph V V V_map V_map V_trie X a0 e0 -> a0.(atom_fn) = sort_of)
          by (intros a0 Ha0; exfalso;
              unfold Semantics.atom_in_egraph, Semantics.atom_in_db in Ha0;
              unfold e0 in Ha0; cbn [Defs.db empty_egraph] in Ha0;
              rewrite map.get_empty in Ha0; exact Ha0).
        specialize (Hframe_vc Huf0 Hdb0 He0_sortof).
        destruct (Hframe_vc a Ha_ectx Hafn_ne) as (x & n_x & s_x & xs_x & Hxin & Htree_e1 & Hnode_e1).
        pose proof (@Core.in_ctx_wf V V_Eqb V_Eqb_ok l c x (scon n_x s_x) Hwf Hwfc Hxin) as Hwst.
        fold e_ctx sub in Htree_e1, Hnode_e1.
        pose proof (@Theorems.atom_tree_sort_survives V V_Eqb V_default V_map V_trie sort_of X l Hsof
                      e_ctx eF sub c Hdb1 Hsurv_ctx (scon n_x s_x) Hwst xs_x Htree_e1) as Htree_eF_sort.
        pose proof (@Theorems.atom_node_sort_survives V V_Eqb V_default V_map V_trie sort_of X l Hsof
                      e_ctx eF sub c Hdb1 Hsurv_ctx n_x s_x Hwst xs_x a Hnode_e1) as Hnode_eF_a.
        assert (Ha_eF_in : atom_in_db V V V_map V_trie X a (db eF))
          by (clear - Hnode_eF_a;
              induction Hnode_eF_a as [n0 s0 sids0 xe0 HF2_0 Hain0
                                      | n0 s0 sids0 xe0 si0 sid0 a0 HF2_0 Hain0 Hcomb0 Hnode0 IH0];
              [unfold Semantics.atom_in_egraph in Hain0; exact Hain0 | exact IH0]).
        assert (Hret_eq : atom_ret a = atom_ret b)
          by (unfold Semantics.atom_in_db, Is_Some_satisfying in Ha_eF_in;
              unfold Semantics.atom_in_egraph, Semantics.atom_in_db, Is_Some_satisfying in Hb;
              rewrite Hafn, Haargs in Ha_eF_in;
              destruct (map.get (Defs.db eF) (atom_fn b)) as [tbl|];
                cbn in Ha_eF_in, Hb; [|contradiction];
              destruct (map.get tbl (atom_args b)) as [entry|];
                cbn in Ha_eF_in, Hb; [|contradiction];
              rewrite <- Hb; exact (eq_sym Ha_eF_in)).
        assert (Hab : a = b)
          by (destruct a as [afn aargs aret]; destruct b as [bfn bargs bret];
              cbn [atom_fn atom_args atom_ret] in *; subst; reflexivity).
        left. exists x, n_x, s_x, xs_x.
        split; [exact Hxin|].
        split; [exact Htree_eF_sort|].
        rewrite <- Hab. exact Hnode_eF_a.
      - (* RIGHT BRANCH: atom_node X e_open sub e1 x1 a *)
        pose proof (@Theorems.atom_node_survives V V_Eqb V_default V_map V_trie sort_of X l Hsof
                      e_open eF sub c Hdb_open Hsurv e1 x1 a Hnode_eopen t Hwfe1) as Hnode_eF_a.
        assert (Ha_eF_in : atom_in_egraph a eF)
          by (apply (@atom_node_ind V V_Eqb V_default V_map V_trie X eF sub
                         (fun _ _ a => atom_in_egraph a eF))
                with (t := e1) (v := x1);
              [ intros n0 s0 sids0 xe0 _ Hain0; exact Hain0
              | intros n0 s0 sids0 xe0 si0 sid0 a0 _ _ _ _ IH0; exact IH0
              | exact Hnode_eF_a ]).
        assert (Hret_eq : atom_ret a = atom_ret b)
          by (unfold Semantics.atom_in_egraph, Semantics.atom_in_db, Is_Some_satisfying in Ha_eF_in, Hb;
              rewrite Hafn in Ha_eF_in;
              rewrite Haargs in Ha_eF_in;
              destruct (map.get (Defs.db eF) (atom_fn b)) as [tbl|];
                cbn in Ha_eF_in, Hb; [|contradiction];
              destruct (map.get tbl (atom_args b)) as [entry|];
                cbn in Ha_eF_in, Hb; [|contradiction];
              rewrite <- Hb; exact (eq_sym Ha_eF_in)).
        assert (Hab : a = b)
          by (destruct a as [afn aargs aret]; destruct b as [bfn bargs bret];
              cbn [atom_fn atom_args atom_ret] in *; subst; reflexivity).
        right. exists x1.
        split; [exact Htree_eF|].
        rewrite <- Hab. exact Hnode_eF_a.
    Qed.

    (* [ctx_readback_eF] on the COMBINED eq-assumption egraph.  Factored
       out of [eq_ctx_inversion]'s body (everything up to [Hrbef]); unlike
       [eq_ctx_inversion] it needs no adversary [a] / soundness hypothesis.
       Used by the eq-adapter coverage lemma [eq_assum_ids_covered]. *)
    Lemma eq_add_ctx_readback_eF (rf : nat) c e1 t
        (Hwfc : wf_ctx l c) (Hwfe1 : wf_term l c e1 t)
        (Hsucc : fst (rebuild rf (snd (add_open_term succ sort_of l false false
                  (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                  e1
                  (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))))
            = Result.Success tt)
      : @CtxReadback.ctx_readback_eF V _ _ V_map V_trie sort_of X
          (snd (rebuild rf (snd (add_open_term succ sort_of l false false
                  (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                  e1
                  (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))))
          (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
          c.
    Proof.
      change (empty_egraph V_default X)
        with (@empty_egraph V V_default V V_map V_map V_trie X) in *.
      set (e0 := @empty_egraph V V_default V V_map V_map V_trie X) in *.
      set (sub := fst (add_ctx succ sort_of l false false c e0)) in *.
      set (e_ctx := snd (add_ctx succ sort_of l false false c e0)) in *.
      set (e_open := snd (add_open_term succ sort_of l false false sub e1 e_ctx)) in *.
      set (eF := snd (rebuild rf e_open)) in *.
      assert (Hok0 : egraph_ok V lt V V_map V_map V_trie X e0)
        by exact (proj1 (@empty_sound_for_interpretation V lt succ V_default V V_map V_map_ok
                           V_map V_map_ok V_trie X lang_model)).
      assert (Huf0 : exists roots, union_find_ok lt (Defs.equiv e0) roots)
        by exact (ex_intro _ [] (@union_find_empty_ok V lt succ V_default V_map V_map_ok)).
      assert (Hdb0 : db_ctx_inv V V_map V_trie sort_of X e0)
        by (intros aa Hin; exfalso;
            unfold Semantics.atom_in_db in Hin;
            unfold e0 in Hin; cbn [Defs.db empty_egraph] in Hin;
            rewrite map.get_empty in Hin; exact Hin).
      pose proof (@Theorems.add_ctx_egraph_ok V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as HE.
      unfold vc in HE. specialize (HE e0).
      fold sub e_ctx in HE.
      specialize (HE Huf0 Hdb0 Hok0).
      destruct HE as (Huf1 & Hdb1 & Hroots1 & Hmapfst & Hok1).
      pose proof (@Theorems.add_ctx_readback V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as HR.
      unfold vc in HR. specialize (HR e0).
      fold sub e_ctx in HR.
      specialize (HR Huf0 Hdb0).
      destruct HR as (_ & _ & _ & _ & Hrb).
      assert (Hmapfst' : map fst c = map fst sub) by (symmetry; exact Hmapfst).
      pose proof (@Theorems.add_open_term_all_roots V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                    c sub e1 t Hwfe1 Hwfc Hmapfst') as Hroots.
      unfold vc in Hroots. specialize (Hroots e_ctx).
      fold e_open in Hroots.
      unfold Theorems.open_roots_post in Hroots.
      specialize (Hroots Huf1 Hdb1 Hroots1).
      fold e_open in Hroots.
      destruct Hroots as (Henv & _).
      unfold Theorems.roots_env in Henv.
      destruct Henv as (Huf_open & Hdb_open & Hdb_incl & Hroots_mono).
      assert (Hbase_keys : all (fun p => Sep.has_key (snd p) (parent (Defs.equiv e_ctx))) sub)
        by (eapply all_wkn; [| exact Hroots1];
            intros p _ Hp; apply (Theorems.is_root_has_key V V_map V_trie X e_ctx (snd p)); exact Hp).
      pose proof (add_ctx_good_worklist_vc c Hwfc) as Hvc_full.
      unfold vc in Hvc_full. specialize (Hvc_full e0).
      assert (Hpke0 : parents_keys_in_equiv V V V_map V_map V_trie X e0)
        by (intros y [s Hs]; unfold e0 in Hs; cbn [parents empty_egraph] in Hs;
            rewrite map.get_empty in Hs; discriminate).
      assert (Hac0 : SemanticsAnalysesCover.analyses_cover V V V_map V_map V_trie X e0)
        by (intros z Hz; exfalso; unfold Sep.has_key in Hz; unfold e0 in Hz;
            cbn [equiv empty_egraph UnionFind.parent UnionFind.empty] in Hz;
            rewrite map.get_empty in Hz; exact Hz).
      assert (Hwl0 : Defs.worklist e0 = []) by reflexivity.
      specialize (Hvc_full Huf0
                           (fun aa Hin => ltac:(exfalso; unfold Semantics.atom_in_db in Hin;
                                                unfold e0 in Hin; cbn [Defs.db empty_egraph] in Hin;
                                                rewrite map.get_empty in Hin; exact Hin))
                           Hok0 Hpke0 Hac0 Hwl0).
      destruct Hvc_full as (_ & _ & _ & _ & _ & _ & Hac1 & _).
      fold sub e_ctx in Hac1.
      pose proof (@Theorems.add_open_worklist_frame V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf
                    l (add_open_sort succ sort_of l false false) Hwf (incl_refl l)
                    c Hwfc) as Hwlf.
      pose proof (proj1 Hwlf e1 t Hwfe1 sub Hmapfst') as Hwlf_term.
      unfold vc in Hwlf_term. specialize (Hwlf_term e_ctx).
      unfold Theorems.open_wlframe_post in Hwlf_term.
      specialize (Hwlf_term Hok1 Hac1 Hbase_keys).
      fold e_open in Hwlf_term.
      destruct Hwlf_term as (_ & Hok_open & _ & _ & _).
      unfold add_open_term in e_open.
      fold e_open in Hok_open.
      pose proof (@Theorems.add_open_node_atoms V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                    l (add_open_sort succ sort_of l false false) Hwf (incl_refl l)
                    c Hwfc) as Hnodes.
      pose proof (proj1 Hnodes e1 t Hwfe1 sub Hmapfst') as Hnode_term.
      unfold vc in Hnode_term. specialize (Hnode_term e_ctx).
      unfold Theorems.open_atomtree_post in Hnode_term.
      specialize (Hnode_term Huf1 Hdb1 Hroots1).
      cbn [fst snd] in Hnode_term.
      fold e_open in Hnode_term.
      destruct Hnode_term as (_ & _ & _ & Hext).
      pose proof (@Theorems.ctx_readback_mono V V_Eqb V_default V_map V_trie sort_of X
                    e_ctx e_open sub c Hdb_incl Hroots_mono Hext Hrb) as Hrb_open.
      assert (Hroots_open : all (fun p => is_root V V_map V_trie X e_open (snd p)) sub)
        by (eapply all_wkn; [| exact Hroots1];
            intros p _ Hp; exact (Hroots_mono (snd p) Hp)).
      pose proof (good_worklist_eq_assum c e1 t Hwfc Hwfe1) as Hgwl_open.
      unfold add_open_term in Hgwl_open.
      fold e0 sub e_ctx e_open in Hgwl_open.
      pose proof (@rebuild_survives_canonical V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt X HX l Hwf Hsof
                    e_open rf Hok_open Hgwl_open Hsucc) as Hsurv.
      pose proof (@CtxReadback.ctx_readback_to_eF V V_Eqb V_default V_map V_trie sort_of X l Hsof
                    e_open eF Hdb_open Hsurv c sub Hwfc Hroots_open Hrb_open) as Hrbef.
      exact Hrbef.
    Qed.

    (* ============================================================ *)
    (* SORT_EQ mirror of the term_eq chain above.                    *)
    (* The sort assumption egraph is:                                *)
    (*   rebuild rf (add_open_sort false false sub t1 (add_ctx c))   *)
    (* ============================================================ *)

    Lemma good_worklist_eq_assum_sort c t1 (Hwfc : wf_ctx l c) (Hwft1 : wf_sort l c t1)
      : exists ed_list,
          good_worklist V V V_map V_map V_trie X
            (snd (add_open_sort succ sort_of l false false
                    (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                    t1
                    (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))
            ed_list.
    Proof.
      pose proof (add_ctx_good_worklist_vc c Hwfc) as Hvc.
      unfold vc in Hvc.
      set (e0 := @empty_egraph V V_default V V_map V_map V_trie X) in *.
      specialize (Hvc e0).
      assert (Huf0 : exists roots, union_find_ok lt (Defs.equiv e0) roots).
      { exact (ex_intro _ [] (@union_find_empty_ok V lt succ V_default V_map V_map_ok)). }
      assert (Hdb0 : @db_inv V V V_map V_map V_trie X (fun _ => True) e0).
      { intros aa Hin. exfalso. unfold Semantics.atom_in_db in Hin.
        unfold e0 in Hin. cbn [Defs.db empty_egraph] in Hin.
        rewrite map.get_empty in Hin. exact Hin. }
      assert (Hok0 : egraph_ok V lt V V_map V_map V_trie X e0).
      { exact (proj1 (@empty_sound_for_interpretation V lt succ V_default V V_map V_map_ok
                        V_map V_map_ok V_trie X lang_model)). }
      assert (Hpke0 : parents_keys_in_equiv V V V_map V_map V_trie X e0).
      { intros y [s Hs]. unfold e0 in Hs. cbn [parents empty_egraph] in Hs.
        rewrite map.get_empty in Hs. discriminate. }
      assert (Hac0 : SemanticsAnalysesCover.analyses_cover V V V_map V_map V_trie X e0).
      { intros z Hz. exfalso. unfold Sep.has_key in Hz. unfold e0 in Hz.
        cbn [equiv empty_egraph UnionFind.parent UnionFind.empty] in Hz.
        rewrite map.get_empty in Hz. exact Hz. }
      assert (Hwl0 : Defs.worklist e0 = []).
      { reflexivity. }
      specialize (Hvc Huf0 Hdb0 Hok0 Hpke0 Hac0 Hwl0).
      destruct Hvc as (Huf1 & Hdb1 & Hroots1 & Hmapfst & Hok1 & Hpke1 & Hac1 & [ed_list Hgw]).
      set (sub := fst (add_ctx succ sort_of l false false c e0)) in *.
      set (e_ctx := snd (add_ctx succ sort_of l false false c e0)) in *.
      set (e_open := snd (add_open_sort succ sort_of l false false sub t1 e_ctx)).
      exists ed_list.
      unfold good_worklist in Hgw.
      destruct Hgw as (Hwl_eq & Hnodup & Hall_good & Hdisj & Hdbfalse & Hcov).
      assert (Hmapfst' : map fst c = map fst sub) by (symmetry; exact Hmapfst).
      pose proof (@Theorems.add_open_sort_all_roots V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                    c sub t1 Hwfc Hwft1 Hmapfst') as Hroots.
      unfold vc in Hroots. specialize (Hroots e_ctx).
      fold e_open in Hroots.
      unfold Theorems.open_roots_sort_post in Hroots.
      specialize (Hroots Huf1 Hdb1 Hroots1).
      fold e_open in Hroots.
      destruct Hroots as (Henv & _).
      unfold Theorems.roots_env in Henv.
      destruct Henv as (Huf_open & Hdb_open_ctx & Hdb_incl & Hroots_mono).
      assert (Hbase_keys : all (fun p => Sep.has_key (snd p) (parent (Defs.equiv e_ctx))) sub).
      { eapply all_wkn; [| exact Hroots1].
        intros p _ Hp. apply (Theorems.is_root_has_key V V_map V_trie X e_ctx (snd p)). exact Hp. }
      pose proof (@Theorems.add_open_sort_worklist_frame V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf
                    c sub t1 Hwfc Hwft1 Hmapfst') as Hwlf_sort.
      unfold vc in Hwlf_sort. specialize (Hwlf_sort e_ctx).
      unfold Theorems.open_wlframe_sort_post, Theorems.open_wlframe_post in Hwlf_sort.
      specialize (Hwlf_sort Hok1 Hac1 Hbase_keys).
      fold e_open in Hwlf_sort.
      destruct Hwlf_sort as (Hwl_open & Hok_open & _ & Hmono_key & _).
      fold e_open in Hwl_open, Hok_open, Hmono_key.
      pose proof (@Theorems.add_open_sort_node_atoms V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                    c sub t1 Hwfc Hwft1 Hmapfst') as Hnode_sort.
      unfold vc in Hnode_sort. specialize (Hnode_sort e_ctx).
      unfold Theorems.open_atomtree_sort_post in Hnode_sort.
      specialize (Hnode_sort Huf1 Hdb1 Hroots1).
      cbn [fst snd] in Hnode_sort.
      fold e_open in Hnode_sort.
      destruct Hnode_sort as (_ & _ & _ & Hext).
      pose proof (@Theorems.add_open_sort_parents_frame V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                    c sub t1 Hwfc Hwft1 Hmapfst') as Hpf_sort.
      unfold vc in Hpf_sort. specialize (Hpf_sort e_ctx).
      unfold Theorems.open_parents_frame_sort_post, Theorems.open_parents_frame_post in Hpf_sort.
      fold e_open in Hpf_sort.
      specialize (Hpf_sort Hok1 Huf1 Hdb1 Hroots1).
      unfold good_worklist.
      split.
      { rewrite Hwl_open. exact Hwl_eq. }
      split.
      { exact Hnodup. }
      split.
      { apply all_via_in_local. intros d Hd_in.
        pose proof (in_all _ _ _ Hall_good Hd_in) as Hgd.
        unfold good_ed in Hgd |- *.
        destruct Hgd as (Hpar_d & Hatom_d & Hargs_d & Hret_d & Hnew_d & Hne_d & Huf_d).
        assert (Hhk_old : Sep.has_key (ed_old V V d) (parent (Defs.equiv e_ctx))).
        { apply Hpke1. exists [ed_atom V V d]. exact Hpar_d. }
        assert (Hnew_open : map.get (parent (Defs.equiv e_open)) (ed_new V V d) = Some (ed_new V V d)).
        { exact (Hroots_mono (ed_new V V d) Hnew_d). }
        assert (Huf_open_d : uf_rel_PER V (V_map V) (V_map nat) (Defs.equiv e_open) (ed_old V V d) (ed_new V V d)).
        { exact (Hext (ed_old V V d) (ed_new V V d) Huf_d). }
        assert (Hnr_old_open : ~ Semantics.is_root V V V_map V_map V_trie X e_open (ed_old V V d)).
        { intro Hroot_old.
          destruct Huf_open as [roots_open Hroots_open].
          exact (Hne_d (@Semantics.roots_uf_rel_eq V V_Eqb V_Eqb_ok lt V_default V_map V_map_ok
                          (Defs.equiv e_open) roots_open (ed_old V V d) (ed_new V V d) Hroots_open
                          Hroot_old Hnew_open Huf_open_d)). }
        split.
        { rewrite (Hpf_sort (ed_old V V d) Hhk_old Hnr_old_open). exact Hpar_d. }
        split. { exact (Hdb_incl (ed_atom V V d) Hatom_d). }
        split. { eapply all_wkn; [| exact Hargs_d]. intros z _ Hz. exact (Hroots_mono z Hz). }
        split. { exact Hret_d. }
        split. { exact Hnew_open. }
        split. { exact Hne_d. }
        { exact Huf_open_d. } }
      split.
      { exact Hdisj. }
      split.
      { unfold db_inv. intros a Ha.
        destruct (Hdb_open_ctx a Ha) as [Hargs_roots _].
        split; [exact Hargs_roots | intro HF; destruct HF]. }
      { intros b Hb_open Hnr_open.
        assert (Hfn_eq : atom_fn b = sort_of).
        { destruct (Hdb_open_ctx b Hb_open) as [_ Hret_root].
          pose proof (V_Eqb_ok (atom_fn b) sort_of) as Heqb_case.
          destruct (eqb (atom_fn b) sort_of) eqn:Heqb.
          - exact Heqb_case.
          - exfalso. apply Hnr_open. exact (Hret_root Heqb_case). }
        assert (Hb_ctx : atom_in_db V V V_map V_trie X b (Defs.db e_ctx)).
        { pose proof (@Theorems.add_open_sort'_keeps_sortof V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                        V_trie succ sort_of lt X HX l Hsof
                        (S (length l)) sub t1 e_ctx) as Hkeeps.
          unfold Semantics.atom_in_db, Is_Some_satisfying in Hb_open |- *.
          rewrite Hfn_eq in Hb_open |- *.
          unfold add_open_sort in Hb_open.
          rewrite <- Hkeeps. exact Hb_open. }
        assert (Hnr_ctx : ~ Semantics.is_root V V V_map V_map V_trie X e_ctx (atom_ret b)).
        { intro Hr_ctx. apply Hnr_open. exact (Hroots_mono (atom_ret b) Hr_ctx). }
        exact (Hcov b Hb_ctx Hnr_ctx). }
    Qed.

    Lemma eq_sort_ctx_inversion (rf : nat) (a : interp) c t1
        (Hwfc : wf_ctx l c) (Hwft1 : wf_sort l c t1)
      : fst (rebuild rf (snd (add_open_sort succ sort_of l false false
                  (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                  t1
                  (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))))
            = Result.Success tt ->
        (forall al, @Semantics.atom_in_egraph V V V_map V_map V_trie X al
                (snd (rebuild rf (snd (add_open_sort succ sort_of l false false
                  (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                  t1
                  (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))))
              -> @Semantics.atom_sound_for_model V V V_map lang_model a al) ->
        exists sg, wf_subst l [] sg c
                /\ map fst sg = map fst c
                /\ (forall x, In x (map fst (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))) ->
                      map.get a (named_list_lookup default
                                  (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))) x)
                        = Some (inl (named_list_lookup default sg x))).
    Proof.
      intros Hsucc Hsound.
      change (empty_egraph V_default X)
        with (@empty_egraph V V_default V V_map V_map V_trie X) in *.
      set (e0 := @empty_egraph V V_default V V_map V_map V_trie X) in *.
      set (sub := fst (add_ctx succ sort_of l false false c e0)) in *.
      set (e_ctx := snd (add_ctx succ sort_of l false false c e0)) in *.
      set (e_open := snd (add_open_sort succ sort_of l false false sub t1 e_ctx)) in *.
      set (eF := snd (rebuild rf e_open)) in *.
      assert (Hok0 : egraph_ok V lt V V_map V_map V_trie X e0)
        by exact (proj1 (@empty_sound_for_interpretation V lt succ V_default V V_map V_map_ok
                           V_map V_map_ok V_trie X lang_model)).
      assert (Huf0 : exists roots, union_find_ok lt (Defs.equiv e0) roots)
        by exact (ex_intro _ [] (@union_find_empty_ok V lt succ V_default V_map V_map_ok)).
      assert (Hdb0 : db_ctx_inv V V_map V_trie sort_of X e0)
        by (intros aa Hin; exfalso;
            unfold Semantics.atom_in_db in Hin;
            unfold e0 in Hin; cbn [Defs.db empty_egraph] in Hin;
            rewrite map.get_empty in Hin; exact Hin).
      pose proof (@Theorems.add_ctx_egraph_ok V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as HE.
      unfold vc in HE. specialize (HE e0).
      fold sub e_ctx in HE.
      specialize (HE Huf0 Hdb0 Hok0).
      destruct HE as (Huf1 & Hdb1 & Hroots1 & Hmapfst & Hok1).
      pose proof (@Theorems.add_ctx_readback V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as HR.
      unfold vc in HR. specialize (HR e0).
      fold sub e_ctx in HR.
      specialize (HR Huf0 Hdb0).
      destruct HR as (_ & _ & _ & _ & Hrb).
      assert (Hmapfst' : map fst c = map fst sub) by (symmetry; exact Hmapfst).
      pose proof (@Theorems.add_open_sort_all_roots V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                    c sub t1 Hwfc Hwft1 Hmapfst') as Hroots.
      unfold vc in Hroots. specialize (Hroots e_ctx).
      fold e_open in Hroots.
      unfold Theorems.open_roots_sort_post in Hroots.
      specialize (Hroots Huf1 Hdb1 Hroots1).
      fold e_open in Hroots.
      destruct Hroots as (Henv & _).
      unfold Theorems.roots_env in Henv.
      destruct Henv as (Huf_open & Hdb_open & Hdb_incl & Hroots_mono).
      assert (Hbase_keys : all (fun p => Sep.has_key (snd p) (parent (Defs.equiv e_ctx))) sub)
        by (eapply all_wkn; [| exact Hroots1];
            intros p _ Hp; apply (Theorems.is_root_has_key V V_map V_trie X e_ctx (snd p)); exact Hp).
      pose proof (add_ctx_good_worklist_vc c Hwfc) as Hvc_full.
      unfold vc in Hvc_full. specialize (Hvc_full e0).
      assert (Hpke0 : parents_keys_in_equiv V V V_map V_map V_trie X e0)
        by (intros y [s Hs]; unfold e0 in Hs; cbn [parents empty_egraph] in Hs;
            rewrite map.get_empty in Hs; discriminate).
      assert (Hac0 : SemanticsAnalysesCover.analyses_cover V V V_map V_map V_trie X e0)
        by (intros z Hz; exfalso; unfold Sep.has_key in Hz; unfold e0 in Hz;
            cbn [equiv empty_egraph UnionFind.parent UnionFind.empty] in Hz;
            rewrite map.get_empty in Hz; exact Hz).
      assert (Hwl0 : Defs.worklist e0 = []) by reflexivity.
      specialize (Hvc_full Huf0
                           (fun aa Hin => ltac:(exfalso; unfold Semantics.atom_in_db in Hin;
                                                unfold e0 in Hin; cbn [Defs.db empty_egraph] in Hin;
                                                rewrite map.get_empty in Hin; exact Hin))
                           Hok0 Hpke0 Hac0 Hwl0).
      destruct Hvc_full as (_ & _ & _ & _ & _ & _ & Hac1 & _).
      fold sub e_ctx in Hac1.
      pose proof (@Theorems.add_open_sort_worklist_frame V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf
                    c sub t1 Hwfc Hwft1 Hmapfst') as Hwlf_sort.
      unfold vc in Hwlf_sort. specialize (Hwlf_sort e_ctx).
      unfold Theorems.open_wlframe_sort_post, Theorems.open_wlframe_post in Hwlf_sort.
      specialize (Hwlf_sort Hok1 Hac1 Hbase_keys).
      fold e_open in Hwlf_sort.
      destruct Hwlf_sort as (_ & Hok_open & _ & _ & _).
      fold e_open in Hok_open.
      pose proof (@Theorems.add_open_sort_node_atoms V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                    c sub t1 Hwfc Hwft1 Hmapfst') as Hnodes_sort.
      unfold vc in Hnodes_sort. specialize (Hnodes_sort e_ctx).
      unfold Theorems.open_atomtree_sort_post in Hnodes_sort.
      specialize (Hnodes_sort Huf1 Hdb1 Hroots1).
      cbn [fst snd] in Hnodes_sort.
      fold e_open in Hnodes_sort.
      destruct Hnodes_sort as (_ & _ & _ & Hext).
      pose proof (@Theorems.ctx_readback_mono V V_Eqb V_default V_map V_trie sort_of X
                    e_ctx e_open sub c Hdb_incl Hroots_mono Hext Hrb) as Hrb_open.
      assert (Hroots_open : all (fun p => is_root V V_map V_trie X e_open (snd p)) sub)
        by (eapply all_wkn; [| exact Hroots1];
            intros p _ Hp; exact (Hroots_mono (snd p) Hp)).
      pose proof (good_worklist_eq_assum_sort c t1 Hwfc Hwft1) as Hgwl_open.
      fold e0 sub e_ctx e_open in Hgwl_open.
      pose proof (@rebuild_survives_canonical V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt X HX l Hwf Hsof
                    e_open rf Hok_open Hgwl_open Hsucc) as Hsurv.
      pose proof (@CtxReadback.ctx_readback_to_eF V V_Eqb V_default V_map V_trie sort_of X l Hsof
                    e_open eF Hdb_open Hsurv c sub Hwfc Hroots_open Hrb_open) as Hrbef.
      exact (@CtxReadback.ctx_readback_wf_subst V V_Eqb V_Eqb_ok V_default V_map V_trie sort_of X l Hwf Hsof
               eF a Hsound c sub Hwfc (eq_sym Hmapfst) Hrbef).
    Qed.

    (* Sort analogue of [eq_ctx_inversion_gen] (the SAME confined admit, for
       the sort_eq query [add_ctx_gen ... no_sort c] with [add_open_sort t1]).
       [Hskip]: a skipped var occurs in the LHS sort [t1].  Admitted for the
       identical reason as [eq_ctx_inversion_gen] (see its comment / memory
       min_sorts_query). *)
    Lemma eq_sort_ctx_inversion_gen (no_sort : V -> bool) (rf : nat) (a : interp) c t1
        (Hwfc : wf_ctx l c) (Hwft1 : wf_sort l c t1)
        (Hskip : forall x, no_sort x = true -> In x (fv_sort t1))
      : fst (rebuild rf (snd (add_open_sort succ sort_of l false false
                  (fst (add_ctx_gen succ sort_of l false false no_sort c (empty_egraph V_default X)))
                  t1
                  (snd (add_ctx_gen succ sort_of l false false no_sort c (empty_egraph V_default X))))))
            = Result.Success tt ->
        (forall al, @Semantics.atom_in_egraph V V V_map V_map V_trie X al
                (snd (rebuild rf (snd (add_open_sort succ sort_of l false false
                  (fst (add_ctx_gen succ sort_of l false false no_sort c (empty_egraph V_default X)))
                  t1
                  (snd (add_ctx_gen succ sort_of l false false no_sort c (empty_egraph V_default X)))))))
              -> @Semantics.atom_sound_for_model V V V_map lang_model a al) ->
        exists sg, wf_subst l [] sg c
                /\ map fst sg = map fst c
                /\ (forall x, In x (map fst (fst (add_ctx_gen succ sort_of l false false no_sort c (empty_egraph V_default X)))) ->
                      map.get a (named_list_lookup default
                                  (fst (add_ctx_gen succ sort_of l false false no_sort c (empty_egraph V_default X))) x)
                        = Some (inl (named_list_lookup default sg x))).
    Proof.
    Admitted.

    Lemma eq_sort_add_ctx_readback_eF (rf : nat) c t1
        (Hwfc : wf_ctx l c) (Hwft1 : wf_sort l c t1)
        (Hsucc : fst (rebuild rf (snd (add_open_sort succ sort_of l false false
                  (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                  t1
                  (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))))
            = Result.Success tt)
      : @CtxReadback.ctx_readback_eF V _ _ V_map V_trie sort_of X
          (snd (rebuild rf (snd (add_open_sort succ sort_of l false false
                  (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                  t1
                  (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))))
          (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
          c.
    Proof.
      change (empty_egraph V_default X)
        with (@empty_egraph V V_default V V_map V_map V_trie X) in *.
      set (e0 := @empty_egraph V V_default V V_map V_map V_trie X) in *.
      set (sub := fst (add_ctx succ sort_of l false false c e0)) in *.
      set (e_ctx := snd (add_ctx succ sort_of l false false c e0)) in *.
      set (e_open := snd (add_open_sort succ sort_of l false false sub t1 e_ctx)) in *.
      set (eF := snd (rebuild rf e_open)) in *.
      assert (Hok0 : egraph_ok V lt V V_map V_map V_trie X e0)
        by exact (proj1 (@empty_sound_for_interpretation V lt succ V_default V V_map V_map_ok
                           V_map V_map_ok V_trie X lang_model)).
      assert (Huf0 : exists roots, union_find_ok lt (Defs.equiv e0) roots)
        by exact (ex_intro _ [] (@union_find_empty_ok V lt succ V_default V_map V_map_ok)).
      assert (Hdb0 : db_ctx_inv V V_map V_trie sort_of X e0)
        by (intros aa Hin; exfalso;
            unfold Semantics.atom_in_db in Hin;
            unfold e0 in Hin; cbn [Defs.db empty_egraph] in Hin;
            rewrite map.get_empty in Hin; exact Hin).
      pose proof (@Theorems.add_ctx_egraph_ok V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as HE.
      unfold vc in HE. specialize (HE e0).
      fold sub e_ctx in HE.
      specialize (HE Huf0 Hdb0 Hok0).
      destruct HE as (Huf1 & Hdb1 & Hroots1 & Hmapfst & Hok1).
      pose proof (@Theorems.add_ctx_readback V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as HR.
      unfold vc in HR. specialize (HR e0).
      fold sub e_ctx in HR.
      specialize (HR Huf0 Hdb0).
      destruct HR as (_ & _ & _ & _ & Hrb).
      assert (Hmapfst' : map fst c = map fst sub) by (symmetry; exact Hmapfst).
      pose proof (@Theorems.add_open_sort_all_roots V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                    c sub t1 Hwfc Hwft1 Hmapfst') as Hroots.
      unfold vc in Hroots. specialize (Hroots e_ctx).
      fold e_open in Hroots.
      unfold Theorems.open_roots_sort_post in Hroots.
      specialize (Hroots Huf1 Hdb1 Hroots1).
      fold e_open in Hroots.
      destruct Hroots as (Henv & _).
      unfold Theorems.roots_env in Henv.
      destruct Henv as (Huf_open & Hdb_open & Hdb_incl & Hroots_mono).
      assert (Hbase_keys : all (fun p => Sep.has_key (snd p) (parent (Defs.equiv e_ctx))) sub)
        by (eapply all_wkn; [| exact Hroots1];
            intros p _ Hp; apply (Theorems.is_root_has_key V V_map V_trie X e_ctx (snd p)); exact Hp).
      pose proof (add_ctx_good_worklist_vc c Hwfc) as Hvc_full.
      unfold vc in Hvc_full. specialize (Hvc_full e0).
      assert (Hpke0 : parents_keys_in_equiv V V V_map V_map V_trie X e0)
        by (intros y [s Hs]; unfold e0 in Hs; cbn [parents empty_egraph] in Hs;
            rewrite map.get_empty in Hs; discriminate).
      assert (Hac0 : SemanticsAnalysesCover.analyses_cover V V V_map V_map V_trie X e0)
        by (intros z Hz; exfalso; unfold Sep.has_key in Hz; unfold e0 in Hz;
            cbn [equiv empty_egraph UnionFind.parent UnionFind.empty] in Hz;
            rewrite map.get_empty in Hz; exact Hz).
      assert (Hwl0 : Defs.worklist e0 = []) by reflexivity.
      specialize (Hvc_full Huf0
                           (fun aa Hin => ltac:(exfalso; unfold Semantics.atom_in_db in Hin;
                                                unfold e0 in Hin; cbn [Defs.db empty_egraph] in Hin;
                                                rewrite map.get_empty in Hin; exact Hin))
                           Hok0 Hpke0 Hac0 Hwl0).
      destruct Hvc_full as (_ & _ & _ & _ & _ & _ & Hac1 & _).
      fold sub e_ctx in Hac1.
      pose proof (@Theorems.add_open_sort_worklist_frame V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf
                    c sub t1 Hwfc Hwft1 Hmapfst') as Hwlf_sort.
      unfold vc in Hwlf_sort. specialize (Hwlf_sort e_ctx).
      unfold Theorems.open_wlframe_sort_post, Theorems.open_wlframe_post in Hwlf_sort.
      specialize (Hwlf_sort Hok1 Hac1 Hbase_keys).
      fold e_open in Hwlf_sort.
      destruct Hwlf_sort as (_ & Hok_open & _ & _ & _).
      fold e_open in Hok_open.
      pose proof (@Theorems.add_open_sort_node_atoms V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                    c sub t1 Hwfc Hwft1 Hmapfst') as Hnodes_sort.
      unfold vc in Hnodes_sort. specialize (Hnodes_sort e_ctx).
      unfold Theorems.open_atomtree_sort_post in Hnodes_sort.
      specialize (Hnodes_sort Huf1 Hdb1 Hroots1).
      cbn [fst snd] in Hnodes_sort.
      fold e_open in Hnodes_sort.
      destruct Hnodes_sort as (_ & _ & _ & Hext).
      pose proof (@Theorems.ctx_readback_mono V V_Eqb V_default V_map V_trie sort_of X
                    e_ctx e_open sub c Hdb_incl Hroots_mono Hext Hrb) as Hrb_open.
      assert (Hroots_open : all (fun p => is_root V V_map V_trie X e_open (snd p)) sub)
        by (eapply all_wkn; [| exact Hroots1];
            intros p _ Hp; exact (Hroots_mono (snd p) Hp)).
      pose proof (good_worklist_eq_assum_sort c t1 Hwfc Hwft1) as Hgwl_open.
      fold e0 sub e_ctx e_open in Hgwl_open.
      pose proof (@rebuild_survives_canonical V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt X HX l Hwf Hsof
                    e_open rf Hok_open Hgwl_open Hsucc) as Hsurv.
      pose proof (@CtxReadback.ctx_readback_to_eF V V_Eqb V_default V_map V_trie sort_of X l Hsof
                    e_open eF Hdb_open Hsurv c sub Hwfc Hroots_open Hrb_open) as Hrbef.
      exact Hrbef.
    Qed.

    Lemma eq_sort_assum_sortof_frame_eF (rf : nat) c t1
      (Hwfc : wf_ctx l c) (Hwft1 : wf_sort l c t1)
      (Hsucc : fst (rebuild rf (snd (add_open_sort succ sort_of l false false
                  (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                  t1
                  (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))))
               = Result.Success tt)
      : forall b,
          @Semantics.atom_in_egraph V V V_map V_map V_trie X b
            (snd (rebuild rf (snd (add_open_sort succ sort_of l false false
                (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                t1
                (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))))) ->
          b.(atom_fn) = sort_of ->
          exists nm x', b.(atom_args) = [x'] /\
            In (nm, x') (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X))).
    Proof.
      intros b Hb Hbfn.
      change (empty_egraph V_default X)
        with (@empty_egraph V V_default V V_map V_map V_trie X) in *.
      set (e0 := @empty_egraph V V_default V V_map V_map V_trie X) in *.
      set (sub := fst (add_ctx succ sort_of l false false c e0)) in *.
      set (e_ctx := snd (add_ctx succ sort_of l false false c e0)) in *.
      set (e_open := snd (add_open_sort succ sort_of l false false sub t1 e_ctx)) in *.
      set (eF := snd (rebuild rf e_open)) in *.
      assert (Hok0 : egraph_ok V lt V V_map V_map V_trie X e0)
        by exact (proj1 (@empty_sound_for_interpretation V lt succ V_default V V_map V_map_ok
                           V_map V_map_ok V_trie X lang_model)).
      assert (Huf0 : exists roots, union_find_ok lt (Defs.equiv e0) roots)
        by exact (ex_intro _ [] (@union_find_empty_ok V lt succ V_default V_map V_map_ok)).
      assert (Hdb0 : db_ctx_inv V V_map V_trie sort_of X e0)
        by (intros aa Hin; exfalso;
            unfold Semantics.atom_in_db in Hin;
            unfold e0 in Hin; cbn [Defs.db empty_egraph] in Hin;
            rewrite map.get_empty in Hin; exact Hin).
      pose proof (@Theorems.add_ctx_egraph_ok V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as HE.
      unfold vc in HE. specialize (HE e0).
      fold sub e_ctx in HE.
      specialize (HE Huf0 Hdb0 Hok0).
      destruct HE as (Huf1 & Hdb1 & Hroots1 & Hmapfst_sub & Hok1).
      assert (Hmapfst' : map fst c = map fst sub) by (symmetry; exact Hmapfst_sub).
      fold sub e_ctx in Huf1, Hdb1, Hroots1, Hmapfst_sub, Hok1.
      pose proof (@Theorems.add_open_sort_node_atoms V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                    c sub t1 Hwfc Hwft1 Hmapfst') as Hnodes_sort.
      unfold vc in Hnodes_sort. specialize (Hnodes_sort e_ctx).
      unfold Theorems.open_atomtree_sort_post in Hnodes_sort.
      specialize (Hnodes_sort Huf1 Hdb1 Hroots1).
      cbn [fst snd] in Hnodes_sort.
      fold e_open in Hnodes_sort.
      destruct Hnodes_sort as (Henv_open & _ & _ & _).
      unfold Theorems.roots_env in Henv_open.
      destruct Henv_open as (Huf_open & Hdb_open & Hdb_incl & Hroots_mono).
      fold sub e_ctx in Huf1, Hdb1, Hroots1, Hmapfst_sub, Hok1.
      assert (Hbase_keys : all (fun p => Sep.has_key (snd p) (parent (Defs.equiv e_ctx))) sub)
        by (eapply all_wkn; [| exact Hroots1];
            intros p _ Hp; apply (Theorems.is_root_has_key V V_map V_trie X e_ctx (snd p)); exact Hp).
      pose proof (add_ctx_good_worklist_vc c Hwfc) as Hvc_full.
      unfold vc in Hvc_full. specialize (Hvc_full e0).
      assert (Hpke0 : parents_keys_in_equiv V V V_map V_map V_trie X e0)
        by (intros y [s Hs]; unfold e0 in Hs; cbn [parents empty_egraph] in Hs;
            rewrite map.get_empty in Hs; discriminate).
      assert (Hac0 : SemanticsAnalysesCover.analyses_cover V V V_map V_map V_trie X e0)
        by (intros z Hz; exfalso; unfold Sep.has_key in Hz; unfold e0 in Hz;
            cbn [equiv empty_egraph UnionFind.parent UnionFind.empty] in Hz;
            rewrite map.get_empty in Hz; exact Hz).
      assert (Hwl0 : Defs.worklist e0 = []) by reflexivity.
      specialize (Hvc_full Huf0
                           (fun aa Hin => ltac:(exfalso; unfold Semantics.atom_in_db in Hin;
                                                unfold e0 in Hin; cbn [Defs.db empty_egraph] in Hin;
                                                rewrite map.get_empty in Hin; exact Hin))
                           Hok0 Hpke0 Hac0 Hwl0).
      destruct Hvc_full as (_ & _ & _ & _ & _ & _ & Hac1 & _).
      fold sub e_ctx in Hac1.
      pose proof (@Theorems.add_open_sort_worklist_frame V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf
                    c sub t1 Hwfc Hwft1 Hmapfst') as Hwlf_sort.
      unfold vc in Hwlf_sort. specialize (Hwlf_sort e_ctx).
      unfold Theorems.open_wlframe_sort_post, Theorems.open_wlframe_post in Hwlf_sort.
      specialize (Hwlf_sort Hok1 Hac1 Hbase_keys).
      fold e_open in Hwlf_sort.
      destruct Hwlf_sort as (_ & Hok_open & _ & _ & _).
      fold e_open in Hok_open.
      pose proof (good_worklist_eq_assum_sort c t1 Hwfc Hwft1) as Hgwl_open.
      fold e0 sub e_ctx e_open in Hgwl_open.
      pose proof (@rebuild_survives_canonical V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt X HX l Hwf Hsof
                    e_open rf Hok_open Hgwl_open Hsucc) as Hsurv0.
      fold eF in Hsurv0.
      assert (Hrefl_per : forall xl,
                 all (is_root V V_map V_trie X e_open) xl ->
                 all2 (UnionFind.uf_rel_PER V (V_map V) (V_map nat) (Defs.equiv e_open)) xl xl)
        by (induction xl as [|z xl IHxl]; cbn; [trivial|];
            intros [Hz Hxl]; split;
            [apply Relations.PER_clo_base; exact Hz | apply IHxl; exact Hxl]).
      assert (Hsurv : forall a0 : atom,
                 @Semantics.atom_in_egraph V V V_map V_map V_trie X a0 e_open ->
                 all (is_root V V_map V_trie X e_open) (atom_args a0) ->
                 is_root V V_map V_trie X e_open (atom_ret a0) ->
                 @Semantics.atom_in_egraph V V V_map V_map V_trie X a0 eF)
        by (intros a0 Ha0_in Ha0_args Ha0_ret;
            apply Hsurv0; [ | exact Ha0_args | exact Ha0_ret ];
            exists a0; split; [| exact Ha0_in];
            unfold Semantics.atom_canonical_equiv; split; [reflexivity|]; split;
            [apply Hrefl_per; exact Ha0_args | apply Relations.PER_clo_base; exact Ha0_ret]).
      destruct rf as [|fuel]; [exfalso; cbn in Hsucc; discriminate Hsucc|].
      destruct Hgwl_open as [ed_list Hgwl_open].
      pose proof (@rebuild_canon V V_Eqb V_Eqb_ok lt succ V_default
                    V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                    X HX (Theorems.lang_model V sort_of l)
                    (@Theorems.lang_model_ok V V_Eqb V_Eqb_ok sort_of l Hsof Hwf)
                    fuel e_open ed_list Hok_open Hgwl_open) as (HdbT & Hmono & Hrev).
      destruct (Hrev b Hb) as (a & Ha_eopen_db & Hafn & Haargs).
      assert (Hafn_sof : atom_fn a = sort_of) by (rewrite Hafn; exact Hbfn).
      pose proof (@Theorems.add_open_sort'_keeps_sortof V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie succ sort_of lt X HX l Hsof
                    (S (length l)) sub t1 e_ctx) as Hkeeps.
      fold e_open in Hkeeps.
      assert (Ha_ectx_db : atom_in_db V V V_map V_trie X a (Defs.db e_ctx))
        by (unfold Semantics.atom_in_db in Ha_eopen_db |- *;
            rewrite Hafn_sof in Ha_eopen_db |- *;
            unfold add_open_sort in Ha_eopen_db;
            rewrite <- Hkeeps;
            exact Ha_eopen_db).
      pose proof (@Theorems.assum_sortof_frame_pre V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as Hsf_vc.
      unfold vc in Hsf_vc. specialize (Hsf_vc e0).
      fold sub e_ctx in Hsf_vc.
      assert (He0_nosof : forall a0, @Semantics.atom_in_egraph V V V_map V_map V_trie X a0 e0 -> a0.(atom_fn) <> sort_of)
        by (intros a0 Ha0; exfalso;
            unfold Semantics.atom_in_egraph, Semantics.atom_in_db in Ha0;
            unfold e0 in Ha0; cbn [Defs.db empty_egraph] in Ha0;
            rewrite map.get_empty in Ha0; exact Ha0).
      specialize (Hsf_vc Huf0 Hdb0 He0_nosof).
      destruct (Hsf_vc a Ha_ectx_db Hafn_sof) as (nm & x' & Hargs_a & Hin_sub).
      exists nm, x'. split; [ rewrite <- Haargs; exact Hargs_a | exact Hin_sub ].
    Qed.

    Lemma eq_sort_assum_db_frame_eF (rf : nat) c t1
      (Hwfc : wf_ctx l c) (Hwft1 : wf_sort l c t1)
      (Hsucc : fst (rebuild rf (snd (add_open_sort succ sort_of l false false
                  (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                  t1
                  (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))))
               = Result.Success tt)
      : forall b,
          @Semantics.atom_in_egraph V V V_map V_map V_trie X b
            (snd (rebuild rf (snd (add_open_sort succ sort_of l false false
                (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                t1
                (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X))))))) ->
          b.(atom_fn) <> sort_of ->
          exists ns ss xs,
            wf_sort l c (scon ns ss)
            /\ atom_tree_sort V V_map V_trie X
                 (snd (rebuild rf (snd (add_open_sort succ sort_of l false false
                   (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                   t1
                   (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))))
                 (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                 (scon ns ss) xs
            /\ atom_node V V_map V_trie X
                 (snd (rebuild rf (snd (add_open_sort succ sort_of l false false
                   (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                   t1
                   (snd (add_ctx succ sort_of l false false c (empty_egraph V_default X)))))))
                 (fst (add_ctx succ sort_of l false false c (empty_egraph V_default X)))
                 (con ns ss) xs b.
    Proof.
      intros b Hb Hbfn.
      change (empty_egraph V_default X)
        with (@empty_egraph V V_default V V_map V_map V_trie X) in *.
      set (e0 := @empty_egraph V V_default V V_map V_map V_trie X) in *.
      set (sub := fst (add_ctx succ sort_of l false false c e0)) in *.
      set (e_ctx := snd (add_ctx succ sort_of l false false c e0)) in *.
      set (e_open := snd (add_open_sort succ sort_of l false false sub t1 e_ctx)) in *.
      set (x1 := fst (add_open_sort succ sort_of l false false sub t1 e_ctx)) in *.
      set (eF := snd (rebuild rf e_open)) in *.
      assert (Hok0 : egraph_ok V lt V V_map V_map V_trie X e0)
        by exact (proj1 (@empty_sound_for_interpretation V lt succ V_default V V_map V_map_ok
                           V_map V_map_ok V_trie X lang_model)).
      assert (Huf0 : exists roots, union_find_ok lt (Defs.equiv e0) roots)
        by exact (ex_intro _ [] (@union_find_empty_ok V lt succ V_default V_map V_map_ok)).
      assert (Hdb0 : db_ctx_inv V V_map V_trie sort_of X e0)
        by (intros aa Hin; exfalso;
            unfold Semantics.atom_in_db in Hin;
            unfold e0 in Hin; cbn [Defs.db empty_egraph] in Hin;
            rewrite map.get_empty in Hin; exact Hin).
      pose proof (@Theorems.add_ctx_egraph_ok V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as HE.
      unfold vc in HE. specialize (HE e0).
      fold sub e_ctx in HE.
      specialize (HE Huf0 Hdb0 Hok0).
      destruct HE as (Huf1 & Hdb1 & Hroots1 & Hmapfst_sub & Hok1).
      assert (Hmapfst' : map fst c = map fst sub) by (symmetry; exact Hmapfst_sub).
      fold sub e_ctx in Huf1, Hdb1, Hroots1, Hmapfst_sub, Hok1.
      pose proof (@Theorems.add_open_sort_node_atoms V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                    c sub t1 Hwfc Hwft1 Hmapfst') as Hnodes_sort.
      unfold vc in Hnodes_sort. specialize (Hnodes_sort e_ctx).
      unfold Theorems.open_atomtree_sort_post in Hnodes_sort.
      specialize (Hnodes_sort Huf1 Hdb1 Hroots1).
      cbn [fst snd] in Hnodes_sort.
      fold e_open x1 in Hnodes_sort.
      destruct Hnodes_sort as (Henv_open & Hx1_root & Htree_open & Hext).
      unfold Theorems.roots_env in Henv_open.
      destruct Henv_open as (Huf_open & Hdb_open & Hdb_incl & Hroots_mono).
      fold sub e_ctx in Huf1, Hdb1, Hroots1, Hmapfst_sub, Hok1.
      assert (Hbase_keys : all (fun p => Sep.has_key (snd p) (parent (Defs.equiv e_ctx))) sub)
        by (eapply all_wkn; [| exact Hroots1];
            intros p _ Hp; apply (Theorems.is_root_has_key V V_map V_trie X e_ctx (snd p)); exact Hp).
      pose proof (add_ctx_good_worklist_vc c Hwfc) as Hvc_full.
      unfold vc in Hvc_full. specialize (Hvc_full e0).
      assert (Hpke0 : parents_keys_in_equiv V V V_map V_map V_trie X e0)
        by (intros y [s Hs]; unfold e0 in Hs; cbn [parents empty_egraph] in Hs;
            rewrite map.get_empty in Hs; discriminate).
      assert (Hac0 : SemanticsAnalysesCover.analyses_cover V V V_map V_map V_trie X e0)
        by (intros z Hz; exfalso; unfold Sep.has_key in Hz; unfold e0 in Hz;
            cbn [equiv empty_egraph UnionFind.parent UnionFind.empty] in Hz;
            rewrite map.get_empty in Hz; exact Hz).
      assert (Hwl0 : Defs.worklist e0 = []) by reflexivity.
      specialize (Hvc_full Huf0
                           (fun aa Hin => ltac:(exfalso; unfold Semantics.atom_in_db in Hin;
                                                unfold e0 in Hin; cbn [Defs.db empty_egraph] in Hin;
                                                rewrite map.get_empty in Hin; exact Hin))
                           Hok0 Hpke0 Hac0 Hwl0).
      destruct Hvc_full as (_ & _ & _ & _ & _ & _ & Hac1 & _).
      fold sub e_ctx in Hac1.
      pose proof (@Theorems.add_open_sort_worklist_frame V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf
                    c sub t1 Hwfc Hwft1 Hmapfst') as Hwlf_sort.
      unfold vc in Hwlf_sort. specialize (Hwlf_sort e_ctx).
      unfold Theorems.open_wlframe_sort_post, Theorems.open_wlframe_post in Hwlf_sort.
      specialize (Hwlf_sort Hok1 Hac1 Hbase_keys).
      fold e_open in Hwlf_sort.
      destruct Hwlf_sort as (_ & Hok_open & _ & _ & _).
      fold e_open in Hok_open.
      pose proof (good_worklist_eq_assum_sort c t1 Hwfc Hwft1) as Hgwl_open.
      fold e0 sub e_ctx e_open in Hgwl_open.
      pose proof (@rebuild_survives_canonical V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt X HX l Hwf Hsof
                    e_open rf Hok_open Hgwl_open Hsucc) as Hsurv0.
      fold eF in Hsurv0.
      assert (Hrefl_per : forall xl,
                 all (is_root V V_map V_trie X e_open) xl ->
                 all2 (UnionFind.uf_rel_PER V (V_map V) (V_map nat) (Defs.equiv e_open)) xl xl)
        by (induction xl as [|z xl IHxl]; cbn; [trivial|];
            intros [Hz Hxl]; split;
            [apply Relations.PER_clo_base; exact Hz | apply IHxl; exact Hxl]).
      assert (Hsurv : forall a0 : atom,
                 @Semantics.atom_in_egraph V V V_map V_map V_trie X a0 e_open ->
                 all (is_root V V_map V_trie X e_open) (atom_args a0) ->
                 is_root V V_map V_trie X e_open (atom_ret a0) ->
                 @Semantics.atom_in_egraph V V V_map V_map V_trie X a0 eF)
        by (intros a0 Ha0_in Ha0_args Ha0_ret;
            apply Hsurv0; [ | exact Ha0_args | exact Ha0_ret ];
            exists a0; split; [| exact Ha0_in];
            unfold Semantics.atom_canonical_equiv; split; [reflexivity|]; split;
            [apply Hrefl_per; exact Ha0_args | apply Relations.PER_clo_base; exact Ha0_ret]).
      assert (Hsurv_ctx : forall a0 : atom,
                 @Semantics.atom_in_egraph V V V_map V_map V_trie X a0 e_ctx ->
                 all (is_root V V_map V_trie X e_ctx) (atom_args a0) ->
                 is_root V V_map V_trie X e_ctx (atom_ret a0) ->
                 @Semantics.atom_in_egraph V V V_map V_map V_trie X a0 eF)
        by (intros a0 Ha0 Hargs Hret;
            apply Hsurv;
            [ exact (Hdb_incl a0 Ha0)
            | eapply all_wkn; [| exact Hargs]; intros z _ Hz; exact (Hroots_mono z Hz)
            | exact (Hroots_mono _ Hret) ]).
      destruct rf as [|fuel]; [exfalso; cbn in Hsucc; discriminate Hsucc|].
      destruct Hgwl_open as [ed_list Hgwl_open].
      pose proof (@rebuild_canon V V_Eqb V_Eqb_ok lt succ V_default
                    V V_Eqb V_Eqb_ok V_map V_map_ok V_map V_map_ok V_trie V_trie_ok
                    X HX (Theorems.lang_model V sort_of l)
                    (@Theorems.lang_model_ok V V_Eqb V_Eqb_ok sort_of l Hsof Hwf)
                    fuel e_open ed_list Hok_open Hgwl_open) as (HdbT & Hmono & Hrev).
      destruct (Hrev b Hb) as (a & Ha_eopen_db & Hafn & Haargs).
      assert (Ha_eopen : @Semantics.atom_in_egraph V V V_map V_map V_trie X a e_open) by exact Ha_eopen_db.
      assert (Hafn_ne : atom_fn a <> sort_of) by (rewrite Hafn; exact Hbfn).
      destruct t1 as [n_t1 s_t1].
      pose proof (@Theorems.add_open_sort_new_atoms_are_nodes V V_Eqb V_Eqb_ok V_default V_map V_map_ok
                    V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof
                    c sub (scon n_t1 s_t1) Hwfc Hwft1 Hmapfst') as Hnewat.
      unfold vc in Hnewat. specialize (Hnewat e_ctx).
      unfold Theorems.open_newatom_sort_post in Hnewat.
      cbn [fst snd] in Hnewat.
      fold e_open x1 in Hnewat.
      specialize (Hnewat Huf1 Hdb1 Hroots1).
      destruct Hnewat as (_ & _ & _ & _ & Hnew_disj).
      destruct (Hnew_disj a Ha_eopen) as [Ha_ectx | Hnode_eopen].
      - (* LEFT BRANCH: a ∈ e_ctx, use assum_db_frame_pre *)
        pose proof (@Theorems.assum_db_frame_pre V V_Eqb V_Eqb_ok V_default V_map V_map_ok V_trie V_trie_ok succ sort_of lt lt_asymmetric lt_succ lt_trans X HX l Hwf Hsof c Hwfc) as Hframe_vc.
        unfold vc in Hframe_vc. specialize (Hframe_vc e0).
        fold sub e_ctx in Hframe_vc.
        assert (He0_sortof : forall a0, @Semantics.atom_in_egraph V V V_map V_map V_trie X a0 e0 -> a0.(atom_fn) = sort_of)
          by (intros a0 Ha0; exfalso;
              unfold Semantics.atom_in_egraph, Semantics.atom_in_db in Ha0;
              unfold e0 in Ha0; cbn [Defs.db empty_egraph] in Ha0;
              rewrite map.get_empty in Ha0; exact Ha0).
        specialize (Hframe_vc Huf0 Hdb0 He0_sortof).
        destruct (Hframe_vc a Ha_ectx Hafn_ne) as (x & n_x & s_x & xs_x & Hxin & Htree_e1 & Hnode_e1).
        pose proof (@Core.in_ctx_wf V V_Eqb V_Eqb_ok l c x (scon n_x s_x) Hwf Hwfc Hxin) as Hwst.
        fold e_ctx sub in Htree_e1, Hnode_e1.
        pose proof (@Theorems.atom_tree_sort_survives V V_Eqb V_default V_map V_trie sort_of X l Hsof
                      e_ctx eF sub c Hdb1 Hsurv_ctx (scon n_x s_x) Hwst xs_x Htree_e1) as Htree_eF_sort.
        pose proof (@Theorems.atom_node_sort_survives V V_Eqb V_default V_map V_trie sort_of X l Hsof
                      e_ctx eF sub c Hdb1 Hsurv_ctx n_x s_x Hwst xs_x a Hnode_e1) as Hnode_eF_a.
        assert (Ha_eF_in : atom_in_db V V V_map V_trie X a (db eF))
          by (clear - Hnode_eF_a;
              induction Hnode_eF_a as [n0 s0 sids0 xe0 HF2_0 Hain0
                                      | n0 s0 sids0 xe0 si0 sid0 a0 HF2_0 Hain0 Hcomb0 Hnode0 IH0];
              [unfold Semantics.atom_in_egraph in Hain0; exact Hain0 | exact IH0]).
        assert (Hret_eq : atom_ret a = atom_ret b)
          by (unfold Semantics.atom_in_db, Is_Some_satisfying in Ha_eF_in;
              unfold Semantics.atom_in_egraph, Semantics.atom_in_db, Is_Some_satisfying in Hb;
              rewrite Hafn, Haargs in Ha_eF_in;
              destruct (map.get (Defs.db eF) (atom_fn b)) as [tbl|];
                cbn in Ha_eF_in, Hb; [|contradiction];
              destruct (map.get tbl (atom_args b)) as [entry|];
                cbn in Ha_eF_in, Hb; [|contradiction];
              rewrite <- Hb; exact (eq_sym Ha_eF_in)).
        assert (Hab : a = b)
          by (destruct a as [afn aargs aret]; destruct b as [bfn bargs bret];
              cbn [atom_fn atom_args atom_ret] in *; subst; reflexivity).
        exists n_x, s_x, xs_x.
        split; [exact Hwst|].
        split; [exact Htree_eF_sort|].
        rewrite <- Hab. exact Hnode_eF_a.
      - (* RIGHT BRANCH: atom_node X e_open sub (con n_t1 s_t1) x1 a *)
        pose proof (@Theorems.atom_node_sort_survives V V_Eqb V_default V_map V_trie sort_of X l Hsof
                      e_open eF sub c Hdb_open Hsurv n_t1 s_t1 Hwft1 x1 a Hnode_eopen) as Hnode_eF_a.
        pose proof (@Theorems.atom_tree_sort_survives V V_Eqb V_default V_map V_trie sort_of X l Hsof
                      e_open eF sub c Hdb_open Hsurv (scon n_t1 s_t1) Hwft1 x1 Htree_open) as Htree_eF.
        assert (Ha_eF_in : atom_in_egraph a eF)
          by (clear - Hnode_eF_a;
              induction Hnode_eF_a as [n0 s0 sids0 xe0 HF2_0 Hain0
                                      | n0 s0 sids0 xe0 si0 sid0 a0 HF2_0 Hain0 Hcomb0 Hnode0 IH0];
              [unfold Semantics.atom_in_egraph in Hain0; exact Hain0 | exact IH0]).
        assert (Hret_eq : atom_ret a = atom_ret b)
          by (unfold Semantics.atom_in_egraph, Semantics.atom_in_db, Is_Some_satisfying in Ha_eF_in, Hb;
              rewrite Hafn in Ha_eF_in;
              rewrite Haargs in Ha_eF_in;
              destruct (map.get (Defs.db eF) (atom_fn b)) as [tbl|];
                cbn in Ha_eF_in, Hb; [|contradiction];
              destruct (map.get tbl (atom_args b)) as [entry|];
                cbn in Ha_eF_in, Hb; [|contradiction];
              rewrite <- Hb; exact (eq_sym Ha_eF_in)).
        assert (Hab : a = b)
          by (destruct a as [afn aargs aret]; destruct b as [bfn bargs bret];
              cbn [atom_fn atom_args atom_ret] in *; subst; reflexivity).
        exists n_t1, s_t1, x1.
        split; [exact Hwft1|].
        split; [exact Htree_eF|].
        rewrite <- Hab. exact Hnode_eF_a.
    Qed.

  End AddCtxInvert.
End WithVar.
