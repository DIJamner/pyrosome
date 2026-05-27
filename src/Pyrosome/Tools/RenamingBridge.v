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
