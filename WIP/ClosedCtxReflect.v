(* =====================================================================
   SESSION 20 (2026-06-08): the USER'S CLOSED-c'[/s/] reframing.
   ===================================================================== *)
Set Implicit Arguments.

Require Import Lists.List.
Import ListNotations.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core ModelImpls.
Import Core.Notations.

Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
          {V_Eqb_ok : Eqb_ok V_Eqb}
          {V_default : WithDefault V}.

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  Notation term := (@term V).
  Notation var := (@var V).
  Notation con := (@con V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).

  Notation wf_subst l :=
    (wf_subst (Model:= core_model l)).
  Notation wf_args l :=
    (wf_args (Model:= core_model l)).
  Notation wf_ctx l :=
    (wf_ctx (Model:= core_model l)).
  Notation eq_subst l :=
    (eq_subst (Model:= core_model l)).

  (* ------------------------------------------------------------------ *)
  (* well-scoped weakening for sorts (local copy; CutElim is downstream). *)
  Lemma term_ws_incl (t:term) args args'
    : well_scoped args t -> incl args args' -> well_scoped args' t.
  Proof.
    induction t; basic_goal_prep; basic_term_crush.
    generalize dependent l; induction l; basic_goal_prep; basic_term_crush.
  Qed.

  Lemma sort_ws_incl (t:sort) args args'
    : well_scoped args t -> incl args args' -> well_scoped args' t.
  Proof.
    destruct t.
    generalize dependent l; induction l; basic_goal_prep; basic_term_crush.
    eapply term_ws_incl; eauto.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* Closed-subst identity helpers. *)
  Lemma closed_term_subst (e:term) s
    : well_scoped [] e -> e [/s/] = e.
  Proof.
    induction e; basic_goal_prep; basic_term_crush.
    match goal with
    | l0 : list term |- _ => generalize dependent l0
    end.
    intro l0; induction l0; basic_goal_prep; basic_term_crush.
  Qed.

  Lemma closed_args_subst (e:list term) s
    : well_scoped [] e -> e [/s/] = e.
  Proof.
    induction e; basic_goal_prep; basic_term_crush.
    eapply closed_term_subst; eauto.
  Qed.

  Lemma closed_sort_subst (e:sort) s
    : well_scoped [] e -> e [/s/] = e.
  Proof.
    destruct e; basic_goal_prep.
    f_equal; eapply closed_args_subst; auto.
  Qed.

  (* ------------------------------------------------------------------ *)
  (* The pointwise context substitution c'[/s/]. *)
  Definition ctx_subst (s : subst) (c : ctx) : ctx :=
    named_map (sort_subst s) c.

  Lemma ctx_subst_fst s c : map fst (ctx_subst s c) = map fst c.
  Proof.
    induction c as [|[n t] c IH]; cbn; [reflexivity| f_equal; exact IH].
  Qed.

  Lemma ctx_subst_cons s n t c
    : ctx_subst s ((n,t)::c) = (n, t[/s/]) :: ctx_subst s c.
  Proof. reflexivity. Qed.

  Lemma in_ctx_subst s c x t
    : In (x,t) c -> In (x, t[/s/]) (ctx_subst s c).
  Proof.
    induction c as [|[n t0] c IH]; cbn; [tauto|].
    intros [H|H].
    - left. safe_invert H. reflexivity.
    - right. apply IH; exact H.
  Qed.

  Lemma in_ctx_subst_inv s c x t
    : In (x,t) (ctx_subst s c) -> exists t0, In (x,t0) c /\ t = t0[/s/].
  Proof.
    induction c as [|[n t0] c IH]; cbn; [tauto|].
    intros [H|H].
    - safe_invert H. exists t0; split; [left; reflexivity| reflexivity].
    - destruct (IH H) as [t1 [Hin Heq]]. exists t1; split; [right; exact Hin| exact Heq].
  Qed.

  (* substituting a fresh leading binding through a wf ctx is a no-op,
     as long as [s] covers all the ctx's variables and is fresh for [n]. *)
  Lemma ctx_subst_strengthen_cons (l:lang) c n e s
    : wf_lang l ->
      wf_ctx l c ->
      fresh n s ->
      incl (map fst c) (map fst s) ->
      ctx_subst ((n,e)::s) c = ctx_subst s c.
  Proof.
    intros Hwfl Hwfc Hfrn. revert s Hfrn.
    induction c as [|[m t] c IH]; intros s Hfrn Hincl; [reflexivity|].
    apply invert_wf_ctx_cons in Hwfc.
    destruct Hwfc as [Hfrm [Hwfc Hwst]].
    pose proof (wf_lang_implies_ws_noext Hwfl) as Hwsl.
    assert (Hws_t : well_scoped (map fst s) t).
    { eapply sort_ws_incl;
        [ eapply (wf_sort_implies_ws (V_Eqb_ok:=V_Eqb_ok)); [exact Hwsl | exact Hwst] | ].
      eapply incl_tran; [|exact Hincl].
      intros a Ha; cbn [map fst]; right; exact Ha. }
    rewrite !ctx_subst_cons.
    f_equal.
    - f_equal.
      change (t[/(n,e)::s/]) with (apply_subst ((n,e)::s) t).
      erewrite strengthen_subst; [reflexivity | typeclasses eauto | exact Hws_t | exact Hfrn].
    - apply IH; [exact Hwfc | exact Hfrn |].
      eapply incl_tran; [|exact Hincl].
      intros a Ha; cbn [map fst]; right; exact Ha.
  Qed.

  Section __.
    Context (l:lang)
      (Hwfl : wf_lang l).

    Let Hwsl : ws_lang l := wf_lang_implies_ws_noext Hwfl.

  (* well-formedness of the substituted context: closed sorts, wf in []. *)
  Lemma wf_ctx_ctx_subst s c
    : wf_ctx l c ->
      wf_subst l [] s c ->
      wf_ctx l (ctx_subst s c).
  Proof.
    intro Hwfc. revert s.
    induction c as [|[n t] c IH]; intros s Hsub.
    - constructor.
    - safe_invert Hsub.
      apply invert_wf_ctx_cons in Hwfc.
      destruct Hwfc as [Hfr [Hwfc Hwst]].
      rewrite ctx_subst_cons.
      pose proof (wf_subst_dom_eq H2) as Hdom.   (* H2 : wf_subst [] s0 c *)
      assert (Hfrs : fresh n s0) by (unfold fresh; rewrite Hdom; exact Hfr).
      assert (Hincl : incl (map fst c) (map fst s0)) by (rewrite Hdom; apply incl_refl).
      rewrite (ctx_subst_strengthen_cons (l:=l) (c:=c) (n:=n) (s:=s0) e Hwfl Hwfc Hfrs Hincl).
      constructor.
      + (* fresh n (ctx_subst s0 c) *)
        unfold fresh. rewrite ctx_subst_fst.
        exact Hfr.
      + apply IH; [exact Hwfc | exact H2].
      + (* wf_sort l (ctx_subst s0 c) (t[/(n,e0)::s0/]) *)
        (* t over c, fresh of n, so t[/(n,e0)::s0/] = t[/s0/]; it is closed,
           so wf in [] hence in any ctx. *)
        erewrite wf_sort_strengthen_cons with (c':=c); eauto with lang_core.
        eapply (wf_sort_ctx_monotonicity (V_Eqb_ok:=V_Eqb_ok));
          [ exact Hwfl
          | eapply (wf_sort_subst_monotonicity (V_Eqb_ok:=V_Eqb_ok));
              [exact Hwfl | exact Hwst | exact Hwfc | exact H2]
          | apply incl_nil_l ].
  Qed.

  (* ================================================================== *)
  (* CLAIM 1: wf_subst l [] s c  <->  wf_subst l [] s (ctx_subst s c).     *)
  (* (s closedness is implied by wf_subst l [] s c on the forward side;    *)
  (*  the backward side uses closedness of the c[/s/] sorts.)              *)
  (* ================================================================== *)

  Lemma claim1_fwd s c
    : wf_ctx l c ->
      wf_subst l [] s c ->
      wf_subst l [] s (ctx_subst s c).
  Proof.
    intros Hwfc Hsub.
    pose proof (wf_subst_dom_eq Hsub) as Hdom.
    eapply (wf_subst_from_pointwise (V_Eqb_ok:=V_Eqb_ok));
      [ exact Hwfl
      | eapply wf_ctx_ctx_subst; eassumption
      | rewrite ctx_subst_fst; exact Hdom
      | ].
    intros x t' Hin.
    apply in_ctx_subst_inv in Hin.
    destruct Hin as [t0 [Hin0 Heq]]. subst t'.
    (* goal: wf_term l [] (subst_lookup s x) ((t0[/s/])[/s/]) *)
    (* t0[/s/] is closed (t0 wf in c, s : wf_subst []) -> idempotent *)
    assert (Hclosed : well_scoped [] (t0[/s/])).
    { change (well_scoped [] (t0[/s/]))
        with (well_scoped (map fst (@nil (V*sort))) (t0[/s/])).
      eapply (wf_sort_implies_ws (V_Eqb_ok:=V_Eqb_ok)); [ exact Hwsl | ].
      eapply (wf_sort_subst_monotonicity (V_Eqb_ok:=V_Eqb_ok));
        [ exact Hwfl
        | eapply (in_ctx_wf (V_Eqb_ok:=V_Eqb_ok)); [exact Hwfl | exact Hwfc | exact Hin0]
        | exact Hwfc | exact Hsub ]. }
    rewrite (closed_sort_subst (t0[/s/]) s Hclosed).
    eapply (wf_subst_lookup (V_Eqb_ok:=V_Eqb_ok)); [exact Hwfl | exact Hwfc | exact Hsub | exact Hin0].
  Qed.

  Lemma claim1_bwd s c
    : wf_ctx l c ->
      wf_subst l [] s (ctx_subst s c) ->
      wf_subst l [] s c.
  Proof.
    intro Hwfc. revert s.
    induction c as [|[n t] c IH]; intros s Hsub.
    - cbn in Hsub. safe_invert Hsub. constructor.
    - rewrite ctx_subst_cons in Hsub.
      destruct s as [|[k e0] s0]; [safe_invert Hsub|].
      pose proof (wf_subst_dom_eq Hsub) as Hdomfull.
      cbn [map fst] in Hdomfull. injection Hdomfull as Hkn _. subst k.
      safe_invert Hsub.   (* head wf H5 at (t[/(n,e0)::s0/])[/s0/]; tail H1 *)
      apply invert_wf_ctx_cons in Hwfc.
      destruct Hwfc as [Hfr [Hwfc Hwst]].
      pose proof (wf_subst_dom_eq H1) as Hdom0.   (* H1 : wf_subst [] s0 (ctx_subst ((k,e0)::s0) c) *)
      rewrite ctx_subst_fst in Hdom0.
      (* the domain of the subst forces k = n via wf_subst_dom_eq on the whole *)
      assert (Hfrs : fresh n s0) by (unfold fresh; rewrite Hdom0; exact Hfr).
      assert (Hincl : incl (map fst c) (map fst s0)) by (rewrite Hdom0; apply incl_refl).
      rewrite (ctx_subst_strengthen_cons (l:=l) (c:=c) (n:=n) (s:=s0) e0 Hwfl Hwfc Hfrs Hincl) in H1.
      assert (Hsub_c : wf_subst l [] s0 c) by (apply IH; [exact Hwfc | exact H1]).
      constructor.
      + exact Hsub_c.
      + (* head: H5 : wf_term l [] e0 ((t[/(k,e0)::s0/])[/s0/]).
           t fresh of n => t[/(k,e0)::s0/] = t[/s0/]; want wf_term l [] e0 (t[/s0/]). *)
        rewrite (wf_sort_strengthen_cons (l:=l) (c':=c) (n:=n) (t':=t)
                   e0 s0 Hwfl Hwst Hfr Hdom0) in H5.
        (* now H5 : wf_term l [] e0 ((t[/s0/])[/s0/]); t[/s0/] is closed -> idempotent *)
        assert (Hcl : well_scoped [] (t[/s0/])).
        { change (well_scoped [] (t[/s0/]))
            with (well_scoped (map fst (@nil (V*sort))) (t[/s0/])).
          eapply (wf_sort_implies_ws (V_Eqb_ok:=V_Eqb_ok)); [ exact Hwsl | ].
          eapply (wf_sort_subst_monotonicity (V_Eqb_ok:=V_Eqb_ok));
            [ exact Hwfl | exact Hwst | exact Hwfc | exact Hsub_c ]. }
        replace (t[/s0/]) with ((t[/s0/])[/s0/])
          by (apply closed_sort_subst; exact Hcl).
        exact H5.
  Qed.

  (* ================================================================== *)
  (* "closed context": all sorts well-scoped in [].                      *)
  (* For such contexts wf_subst over [] is a flat pointwise condition     *)
  (* (no telescope coupling) and is permutation-invariant.                *)
  (* ================================================================== *)
  Definition closed_ctx (c : ctx) : Prop :=
    forall x t, In (x,t) c -> well_scoped [] t.

  Lemma closed_ctx_ctx_subst s c
    : wf_ctx l c ->
      wf_subst l [] s c ->
      closed_ctx (ctx_subst s c).
  Proof.
    intros Hwfc Hsub x t Hin.
    apply in_ctx_subst_inv in Hin.
    destruct Hin as [t0 [Hin0 Heq]]. subst t.
    change (well_scoped [] (t0[/s/]))
      with (well_scoped (map fst (@nil (V*sort))) (t0[/s/])).
    eapply (wf_sort_implies_ws (V_Eqb_ok:=V_Eqb_ok)); [exact Hwsl|].
    eapply (wf_sort_subst_monotonicity (V_Eqb_ok:=V_Eqb_ok));
      [ exact Hwfl
      | eapply (in_ctx_wf (V_Eqb_ok:=V_Eqb_ok)); [exact Hwfl | exact Hwfc | exact Hin0]
      | exact Hwfc | exact Hsub ].
  Qed.

  (* CLAIM 2 (forward): pointwise reading of wf_subst over a CLOSED ctx.
     The image of each variable is wf at its (already-closed) declared sort. *)
  Lemma claim2_fwd s c'
    : wf_ctx l c' ->
      closed_ctx c' ->
      wf_subst l [] s c' ->
      forall x t, In (x,t) c' -> wf_term l [] (subst_lookup s x) t.
  Proof.
    intros Hwfc Hcl Hsub x t Hin.
    pose proof (wf_subst_lookup (l:=l) (V_Eqb_ok:=V_Eqb_ok) Hwfl
                  (c:=[]) (c':=c') (s:=s) Hwfc Hsub x t Hin) as Hlk.
    rewrite (closed_sort_subst t s (Hcl _ _ Hin)) in Hlk.
    exact Hlk.
  Qed.

  (* CLAIM 2 (backward): the converse.  Over a CLOSED, all-fresh ctx,
     the flat pointwise condition assembles a wf_subst -- there is NO
     telescope/tail-subst coupling because each declared sort is already
     closed (so [t[/s/] = t]). *)
  Lemma claim2_bwd s c'
    : wf_ctx l c' ->
      closed_ctx c' ->
      map fst s = map fst c' ->
      (forall x t, In (x,t) c' -> wf_term l [] (subst_lookup s x) t) ->
      wf_subst l [] s c'.
  Proof.
    intros Hwfc Hcl Hdom Hpt.
    eapply (wf_subst_from_pointwise (V_Eqb_ok:=V_Eqb_ok));
      [ exact Hwfl | exact Hwfc | exact Hdom | ].
    intros x t' Hin.
    (* goal: wf_term l [] (subst_lookup s x) (t'[/s/]); t' closed -> t'[/s/]=t'. *)
    rewrite (closed_sort_subst t' s (Hcl _ _ Hin)).
    eapply Hpt; exact Hin.
  Qed.

  (* ================================================================== *)
  (* PERMUTATION INVARIANCE of wf_subst over a CLOSED ctx.               *)
  (* Because the declared sorts are closed, wf_subst l [] s c' depends    *)
  (* only on the NAME->SORT association, not the order: any reordering    *)
  (* c2 of c' (same membership, all-fresh) with a domain-matching s is    *)
  (* equally well-formed.  This is what lets the c0-order reorder of      *)
  (* c'[/s/] go through.                                                  *)
  (* ================================================================== *)
  Lemma wf_subst_closed_perm s c1 c2
    : wf_ctx l c1 ->
      wf_ctx l c2 ->
      closed_ctx c1 ->
      map fst s = map fst c2 ->
      (forall x t, In (x,t) c2 -> In (x,t) c1) ->
      wf_subst l [] s c1 ->
      wf_subst l [] s c2.
  Proof.
    intros Hwfc1 Hwfc2 Hcl1 Hdom Hsub21 Hsub.
    (* c2's sorts are closed too (membership in c1). *)
    assert (Hcl2 : closed_ctx c2)
      by (intros x t Hin; eapply Hcl1; eapply Hsub21; exact Hin).
    eapply claim2_bwd; [ exact Hwfc2 | exact Hcl2 | exact Hdom | ].
    intros x t Hin2.
    (* read off c1's pointwise (claim2_fwd) at the c1-membership of (x,t). *)
    eapply (claim2_fwd (s:=s) (c':=c1) Hwfc1 Hcl1 Hsub x t).
    eapply Hsub21; exact Hin2.
  Qed.

  End __.
End WithVar.
