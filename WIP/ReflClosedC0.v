(* =====================================================================
   SESSION 20 (2026-06-08): the USER'S CLOSED-c'[/s/] reframing, TESTED
   CONCRETELY AT THE VAR-ARG REFLECTION LEAF.

   We now have (ClosedSubstReflect, all Qed):
     claim1 : wf_subst l [] s c'  <->  wf_subst l [] s (ctx_subst s c')
     claim2 : flat pointwise characterization over a CLOSED ctx
     wf_subst_closed_perm : reorder-invariance over a closed ctx.

   The user's hope: reorder the flat c'[/s/] into c0 order, run the c0-order
   parallel image/source induction, and close the direct-var leaf using the
   closed/flat structure WITHOUT the full wf_subst l [] s c'.

   THIS SCRATCH drives the c0-order induction with the c'[/s/] reframing
   available and exhibits the EXACT residual at the var-arg leaf.

   RESULT (mechanically verified below): the closed/flat reframing does NOT
   close the leaf.  Two independent confirmations:

   (A) By claim1, building wf_subst l [] s (ctx_subst s c') is EQUIVALENT to
       building wf_subst l [] s c'.  So the flat form gives NO new way to
       CONSTRUCT the substitution -- whatever closes the flat form's
       pointwise obligation [wf_term l [] (s x) (t'[/s/])] already closes the
       original.  The flat form's only advantage (permutation, claim2/perm)
       is about REORDERING an ALREADY-BUILT wf_subst, not building it.

   (B) At the var-arg leaf itself (probe_var_leaf_closed below): even with the
       c0-tail wf_substs explicit and the use-sort image t1[/s/] in CLOSED
       form, the residual is still
           eq_sort l [] (t1[/s/]) (t'[/s/])
       and the ONLY bridge is the SOURCE equation
           Heqsrc : eq_sort l c' t1 t'    (over c', via term_sorts_eq)
       transported by s = eq_subst l [] c' s s = the full wf_subst l [] s c'.
       The closed image derivation knows t1[/s/] (the operator USE sort,
       instantiated by closed siblings) but carries NO witness relating it to
       the DECLARED closed sort t'[/s/]: t' is x's sort in c', which never
       appears in the []-image/operator-ctx derivation.  So no closed datum
       provides the conversion; it must come from transporting Heqsrc over c'.
   ===================================================================== *)
Set Implicit Arguments.

Require Import Lists.List.
Import ListNotations.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core ModelImpls ClosedSubstReflect.
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

  Section __.
    Context (l:lang)
      (Hwfl : wf_lang l).

  (* The var-arg leaf, now with the CLOSED-c'[/s/] reframing available.

     We have a direct var arg x at some c0 (operator-ctx cA) slot; the
     parallel source/image wf_args (in c0 order); and CLOSEDNESS of s (which
     holds for all our uses: s comes from the e-graph as []-terms).  We make
     the flat c'[/s/] structure explicit and try to close the leaf with it. *)
  Lemma probe_var_leaf_closed c' c s cA args
    : wf_ctx l c' ->
      wf_ctx l cA ->
      wf_args l c' args cA ->
      map fst s = map fst c' ->
      wf_args l c args[/s/] cA ->
      (* closedness of s (true for engine value maps): each value closed *)
      (forall x e, In (x,e) s -> well_scoped [] e) ->
      forall x t',
        In (x, t') c' ->
        In (var x) args ->
        wf_term l c (subst_lookup s x) t'[/s/].
  Proof.
    intros Hwfc HwfcA Hsrc Hmap Himg Hcls x t' Hin Hocc.
    revert cA HwfcA Hsrc Himg Hocc.
    induction args as [|e0 rest IHargs]; intros cA HwfcA Hsrc Himg Hocc.
    { cbn in Hocc; contradiction. }
    destruct cA as [|[nm tnm] cA'].
    { safe_invert Hsrc. }
    apply invert_wf_ctx_cons in HwfcA.
    destruct HwfcA as [HfrcA [HwfcA' Hwst_tnm]].
    cbn [apply_subst substable_args args_subst map] in Himg.
    safe_invert Hsrc.
    safe_invert Himg.
    cbn [In] in Hocc.
    destruct Hocc as [Hhead | Htail].
    2:{ eapply IHargs; [ exact HwfcA' | eassumption | eassumption | exact Htail ]. }
    subst e0.
    (* the c0-TAIL wf_substs (both sides), via wf_subst_from_wf_args, exactly
       as in ReflC0 -- the "complete c0-prefix wf_substs, for free". *)
    match goal with
    | Hs : wf_args l c' rest cA' |- _ =>
        pose proof (wf_subst_from_wf_args (Model:=core_model l) Hs) as Htsub_src
    end.
    match goal with
    | Hs : wf_args l c (map (term_subst s) rest) cA' |- _ =>
        pose proof (wf_subst_from_wf_args (Model:=core_model l) Hs) as Htsub_img
    end.
    set (t1 := tnm[/with_names_from cA' rest/]) in *.
    match goal with
    | Hh : Model.wf_term c (term_subst s (var x)) _ |- _ => rename Hh into Himgh
    end.
    match goal with
    | Hh : Model.wf_term c' (var x) t1 |- _ => rename Hh into Hsrch
    end.
    cbn [term_subst term_var_map] in Himgh.
    change (term_subst_lookup s x) with (subst_lookup s x) in Himgh.
    assert (Hvar : wf_term l c' (var x) t') by (apply wf_term_var; exact Hin).
    assert (Heqsrc : eq_sort l c' t1 t')
      by (eapply (term_sorts_eq (l:=l));
          [ exact Hwfl | exact Hwfc | exact Hsrch | exact Hvar ]).
    assert (Hlen : length cA' = length rest)
      by (eapply wf_args_length_eq; eassumption).
    assert (Hwst1 : ws_sort (map fst cA') tnm).
    { eapply (wf_sort_implies_ws (V_Eqb_ok:=V_Eqb_ok));
        [ exact (wf_lang_implies_ws_noext Hwfl) | exact Hwst_tnm ]. }
    assert (Himgsort : (t1[/s/]) = (tnm[/with_names_from cA' (map (term_subst s) rest)/])).
    { subst t1.
      change (map (term_subst s) rest) with (rest[/s/]).
      rewrite with_names_from_args_subst.
      erewrite subst_assoc; [ reflexivity | typeclasses eauto | ].
      rewrite map_fst_with_names_from by exact Hlen. exact Hwst1. }
    eapply wf_term_conv; [ exact Himgh |].
    (* ================================================================
       THE LEAF GOAL (after using the CLOSED image sort identity):
           eq_sort l c (t1[/s/]) (t'[/s/])
       In scope (closed-reframing data ALL available):
         Hcls    : s is closed
         Heqsrc  : eq_sort l c' t1 t'        (SOURCE use=declared, over c')
         Himgh   : wf_term l c (s x) (t1[/s/])  (closed use-sort image)
         Htsub_src : wf_subst l c' (wnf cA' rest) cA'    (c0-tail, over c')
         Htsub_img : wf_subst l c  (wnf cA' (rest[/s/])) cA' (c0-tail, over c)
       and (claim1/claim2/perm from ClosedSubstReflect) about ctx_subst.

       NONE of the closed/flat data yields eq_sort l c (t1[/s/]) (t'[/s/]):
       - claim1 says the flat ctx_subst wf_subst is EQUIVALENT to build, so it
         provides no independent witness.
       - the c0-tail substs Htsub_src/Htsub_img are over the OPERATOR ctx cA',
         NOT over c'; they instantiate t1's internal telescoping, not the
         use<->declared link.
       - the closed image (Himgh) knows t1[/s/] but t' (x's c'-sort) never
         appears in any []-/cA'-derivation, so nothing closed relates them.
       The ONLY route is transporting Heqsrc over c', = full wf_subst l c s c'.
       ================================================================ *)
    (* Build the residual at t1[/s/], transport to the image use-sort via
       Himgsort -- exactly as Core.wf_subst_from_args_image does. *)
    assert (Hg : eq_sort l c (t1[/s/]) (t'[/s/])).
    { (* THE WALL: covering_var_leaf_transport of Heqsrc by s needs the FULL
         wf_subst l c s c'.  NO closed/flat datum (claim1/claim2/perm, the
         c0-tail substs, the closed image use-sort) supplies it; see header. *)
      eapply covering_var_leaf_transport;
        [ exact Hwfl | exact Hwfc | exact Hmap
        | (* WALL: wf_subst l c s c' -- the full subst *) admit
        | exact Heqsrc ]. }
    rewrite Himgsort in Hg. exact Hg.
  Admitted.

  (* ==================================================================
     THE CIRCULARITY, MADE MECHANICAL.

     One might hope to discharge the [wf_subst l [] s c'] admit ABOVE via the
     flat [ctx_subst s c'] (claim1_bwd + claim2_bwd), exploiting that it is
     permutation-invariant.  This lemma shows that route reduces EXACTLY to the
     per-variable leaf obligation [wf_term l [] (s x) (t'[/s/])] for every
     (x,t') in c' -- i.e. to the very goal [probe_var_leaf_closed] is proving.
     So the flat reframing provides NO independent way to build the subst: by
     claim1 the flat form is EQUIVALENT to construct, and claim2 unfolds it to
     the same leaves.  (No [admit]; this is a real proof that the reduction is
     circular.) *)
  Lemma flat_route_is_circular s c'
    : wf_ctx l c' ->
      map fst s = map fst c' ->
      (* the per-var leaf obligations (what probe_var_leaf_closed proves): *)
      (forall x t', In (x,t') c' -> wf_term l [] (subst_lookup s x) t'[/s/]) ->
      (* are NECESSARY AND SUFFICIENT for the full wf_subst: *)
      wf_subst l [] s c'.
  Proof.
    intros Hwfc Hmap Hleaves.
    (* The leaves ARE the wf_subst_from_pointwise obligations: no flat detour
       buys anything (claim1: the flat form is equivalent; claim2: it unfolds
       to these same leaves). *)
    eapply (wf_subst_from_pointwise (V_Eqb_ok:=V_Eqb_ok));
      [ exact Hwfl | exact Hwfc | exact Hmap | exact Hleaves ].
  Qed.

  End __.
End WithVar.
