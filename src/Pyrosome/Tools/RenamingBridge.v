(* Bridge lemmas connecting the V<->positive renaming (PosRenaming /
   PosRenamingProperties) with the open<->closed closing (ClosedCore),
   used to discharge the renaming half of [egraph_reducing_equal'_to_pos].

   The egraph runs on [rename_lang (ctx_to_rules c ++ l)] etc.; soundness
   needs to lift an equality proved in the positive, closed world back to
   the original open equality over [l] in context [c].  That lift is
   [reverse_eq_term_lift] below: it composes
   [unrename_preserves_eq_term] (positive -> V, PosRenamingProperties) with
   [eq_rtv] (closed -> open, ClosedCore) and the [*_vtr] round-trips. *)

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope list.
From Stdlib Require Import BinNums.
From coqutil Require Import Map.Interface.
From Utils Require Import Utils.
From Utils Require Import PosListMap.
From Pyrosome.Theory Require Import Core ClosedCore.
From Pyrosome.Theory Require Renaming.
From Pyrosome.Tools Require Import PosRenaming PosRenamingProperties.

Section Bridge.
  Context (V : Type) {V_Eqb : Eqb V} {V_Eqb_ok : Eqb_ok V_Eqb}
    {V_default : WithDefault V}.

  (* The renaming-state initialiser used by [egraph_reducing_equal'] and
     friends is [{| p_to_v := map.empty; v_to_p := {{c}}; next_id := 2 |}],
     where [{{c}}] is a (misleading) notation for the empty list.  It is
     well-formed for the same vacuous reasons as [empty_renaming_ok]; the
     [next_id := 2] (reserving position 1 for [sort_of]) affects no field
     since [v_to_p] is empty. *)
  Lemma init_renaming_ok :
    renaming_ok {| p_to_v := map.empty; v_to_p := []; next_id := xO xH |}.
  Proof.
    constructor; cbn.
    - exact I.
    - intros ? ? [].
    - intros v p Hget; cbn in Hget; congruence.
    - intros ? ? [].
    - intros v1 v2 [] _ _.
  Qed.

  (* The forward state-threading: renaming a closed lang [L], two closed terms
     [E1]/[E2] (well-formed in [L] at [] over sort [T]), and [T] (renamed last,
     at some later state [r6] reached opaquely from [r3]) yields well-formed
     positive outputs AND the bound/unrename-inverts facts at the final state
     [r7] -- exactly the hypotheses [reverse_eq_term_lift] needs.  Forward wf
     goes via [Renaming.rename_mono_S_eq] on [eq_term_refl] (the [via_f]
     machinery, mirroring [rename_preserves_eq_term]); the bounds/unrename use
     the per-op [rename_*_correct] facts grown to [r7]. *)
  Lemma rename_egraph_bridge
      (L : lang V) (E1 E2 : Term.term V) (T : sort V)
      (r0 r1 r2 r3 r6 r7 : renaming V)
      (Lp : lang positive) (E1p E2p : Term.term positive) (Tp : sort positive)
    : wf_lang L -> wf_term L [] E1 T -> wf_term L [] E2 T ->
      renaming_ok r0 ->
      rename_lang L r0 = (Lp, r1) ->
      rename_term E1 r1 = (E1p, r2) ->
      rename_term E2 r2 = (E2p, r3) ->
      renaming_ok r6 -> rename_grows r3 r6 ->
      rename_sort T r6 = (Tp, r7) ->
      wf_lang Lp /\ wf_term Lp [] E1p Tp /\ wf_term Lp [] E2p Tp /\
      renaming_ok r7 /\
      lang_bound r7 Lp /\ term_bound r7 E1p /\ term_bound r7 E2p /\ sort_bound r7 Tp /\
      unrename_lang r7 Lp = L /\ unrename_term r7 E1p = E1 /\
      unrename_term r7 E2p = E2 /\ unrename_sort r7 Tp = T.
  Proof.
    intros HwfL HwfE1 HwfE2 Hr0 HrL HrE1 HrE2 Hr6 Hg36 HrT.
    pose proof (rename_lang_correct _ Hr0 HrL) as (Hr1ok & Hg01 & Hbl1 & Hul1).
    pose proof (rename_term_correct _ Hr1ok HrE1) as (Hr2ok & Hg12 & Hbe1 & Hue1).
    pose proof (rename_term_correct _ Hr2ok HrE2) as (Hr3ok & Hg23 & Hbe2 & Hue2).
    pose proof (rename_sort_correct _ Hr6 HrT) as (Hr7ok & Hg67 & Hbt7 & Hut7).
    pose (Hg17 := rename_grows_trans Hg12 (rename_grows_trans Hg23 (rename_grows_trans Hg36 Hg67))).
    pose (Hg27 := rename_grows_trans Hg23 (rename_grows_trans Hg36 Hg67)).
    pose (Hg37 := rename_grows_trans Hg36 Hg67).
    pose proof (lang_in_keys_of_unrename _ Hr1ok Hbl1) as HlkL. rewrite Hul1 in HlkL.
    pose proof (lang_in_keys_grows Hg17 Hr1ok Hr7ok HlkL) as HlkL7.
    pose proof (term_in_keys_of_unrename _ Hr2ok Hbe1) as HkE1. rewrite Hue1 in HkE1.
    pose proof (term_in_keys_grows Hg27 Hr2ok Hr7ok HkE1) as HkE17.
    pose proof (term_in_keys_of_unrename _ Hr3ok Hbe2) as HkE2. rewrite Hue2 in HkE2.
    pose proof (term_in_keys_grows Hg37 Hr3ok Hr7ok HkE2) as HkE27.
    pose proof (sort_in_keys_of_unrename _ Hr7ok Hbt7) as HkT7. rewrite Hut7 in HkT7.
    set (f := pos_of_v r7) in *.
    pose proof (pos_of_v_matches Hr7ok : f_matches f r7) as Hfm7.
    pose proof (f_matches_grows Hr6 Hr7ok Hg67 Hfm7) as Hfm6.
    pose proof (f_matches_grows Hr3ok Hr6 Hg36 Hfm6) as Hfm3.
    pose proof (f_matches_grows Hr2ok Hr3ok Hg23 Hfm3) as Hfm2.
    pose proof (f_matches_grows Hr1ok Hr2ok Hg12 Hfm2) as Hfm1.
    pose proof (rename_lang_via_f (f:=f) L Hr0 HrL Hfm1) as HLpf.
    pose proof (rename_term_via_f (f:=f) E1 Hr1ok HrE1 Hfm2) as HE1pf.
    pose proof (rename_term_via_f (f:=f) E2 Hr2ok HrE2 Hfm3) as HE2pf.
    pose proof (rename_sort_via_f (f:=f) T Hr6 HrT Hfm7) as HTpf.
    pose proof (pos_of_v_inj_on_keys Hr7ok : Renaming.Injective_on (v_in_keys r7) f) as Hinj.
    assert (wfLp : wf_lang Lp) by exact (rename_lang_preserves_wf_lang HwfL Hr0 HrL).
    assert (HwflF : wf_lang (Renaming.rename_lang f L)) by (rewrite <- HLpf; exact wfLp).
    assert (Hwfnil : wf_ctx (Model:=core_model L) (@nil (V * Term.sort V))) by constructor.
    assert (Hcinil : Renaming.ctx_in_S (v_in_keys r7) (@nil (V * Term.sort V))) by exact I.
    pose proof (Renaming.rename_mono_S_wf_ctx (Eqb_ok_B := positive_Eqb_ok)
                  Hinj HwfL HlkL7 HwflF Hwfnil Hcinil) as HwfcF.
    pose proof (proj1 (proj2 (Renaming.rename_mono_S_eq (Eqb_ok_B := positive_Eqb_ok)
                  Hinj HwfL HlkL7 HwflF Hwfnil Hcinil HwfcF))) as Heqpres.
    pose proof (Heqpres T E1 E1 (eq_term_refl HwfE1) HkT7 HkE17 HkE17) as HeqE1.
    pose proof (Heqpres T E2 E2 (eq_term_refl HwfE2) HkT7 HkE27 HkE27) as HeqE2.
    rewrite <- HLpf, <- HTpf, <- HE1pf in HeqE1.
    rewrite <- HLpf, <- HTpf, <- HE2pf in HeqE2.
    replace (Renaming.rename_ctx f []) with (@nil (positive * Term.sort positive))
      in HeqE1, HeqE2 by reflexivity.
    assert (wfE1 : wf_term Lp [] E1p Tp) by
      (eapply eq_term_wf_l;
       [ exact positive_Eqb_ok | | exact wfLp | constructor | exact HeqE1 ];
       exact PosListMap.positive_default).
    assert (wfE2 : wf_term Lp [] E2p Tp) by
      (eapply eq_term_wf_l;
       [ exact positive_Eqb_ok | | exact wfLp | constructor | exact HeqE2 ];
       exact PosListMap.positive_default).
    repeat (apply conj);
      [ exact wfLp | exact wfE1 | exact wfE2 | exact Hr7ok
      | exact (lang_bound_grows Hg17 Hbl1)
      | exact (term_bound_grows Hg27 Hbe1)
      | exact (term_bound_grows Hg37 Hbe2)
      | exact Hbt7
      | rewrite (unrename_lang_grows Hg17 Hbl1); exact Hul1
      | rewrite (unrename_term_grows Hg27 Hbe1); exact Hue1
      | rewrite (unrename_term_grows Hg37 Hbe2); exact Hue2
      | exact Hut7 ].
  Qed.

  (* The reverse eq_term lift.  Given that the renaming [r] inverts (via
     [unrename_*]) the positive-world data back to the closed string forms
     [ctx_to_rules c ++ l], [vtr e1], [vtr e2], [svtr t], an equality the
     egraph proved (positive, empty ctx) lifts to the original open
     equality [eq_term l c t e1 e2]. *)
  Lemma reverse_eq_term_lift
      (l : lang V) (c : ctx V) (t : sort V) (e1 e2 : Term.term V)
      (r : renaming V) (lp : lang positive) (tp : sort positive)
      (e1p e2p : Term.term positive)
    : wf_lang l ->
      wf_ctx (Model:=core_model l) c ->
      all (fun x => fresh x l) (map fst c) ->
      wf_term l c e1 t ->
      wf_term l c e2 t ->
      renaming_ok r ->
      lang_bound r lp ->
      sort_bound r tp ->
      term_bound r e1p ->
      term_bound r e2p ->
      wf_lang lp ->
      unrename_lang r lp = ctx_to_rules c ++ l ->
      unrename_term r e1p = vtr e1 ->
      unrename_term r e2p = vtr e2 ->
      unrename_sort r tp = svtr t ->
      eq_term lp [] tp e1p e2p ->
      eq_term l c t e1 e2.
  Proof.
    intros wfl wfc Hdisj He1 He2 Hrok Hbl Hbt Hbe1 Hbe2 Hwflp Hul Hue1 Hue2 Hut Heq.
    pose proof (wf_lang_concat wfl (ctx_to_rules_wf wfl wfc Hdisj)) as Hwfl'.
    pose proof (eq_term_wf_sort wfl wfc (eq_term_refl He1)) as Hwfsort.
    pose proof (unrename_preserves_eq_term Hrok Heq Hbl
                  ltac:(exact I) Hbt Hbe1 Hbe2 Hwflp ltac:(constructor)) as Hun.
    rewrite Hul, Hue1, Hue2, Hut in Hun.
    replace (unrename_ctx r []) with (@nil (V * sort V)) in Hun by reflexivity.
    destruct (eq_rtv wfl wfc Hwfl' Hdisj) as [_ [Het _]].
    pose proof (Het (svtr t) (vtr e1) (vtr e2) Hun) as Hrtv.
    rewrite (srtv_svtr_wf wfl wfc Hdisj Hwfsort) in Hrtv.
    rewrite (rtv_vtr_wf wfl wfc Hdisj He1) in Hrtv.
    rewrite (rtv_vtr_wf wfl wfc Hdisj He2) in Hrtv.
    exact Hrtv.
  Qed.

End Bridge.
