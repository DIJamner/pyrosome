(* =====================================================================
   SESSION 19 (2026-06-08): c0-ORDER deconstruction of the var-arg leaf,
   TESTED CONCRETELY IN COQ.

   The user's frame: induct on the c0-telescope (operator ctx), deconstruct
   the parallel source/image wf_args IN c0 ORDER, and close the direct-var
   leaf using the ALREADY-BUILT c0-PREFIX substitution (the c0-tail values),
   never the full sg.  Claim: each c0-step's use-sort depends only on
   c0-earlier args, so the use->declared bridge transports by the prefix.

   THIS SCRATCH WORKS THAT FRAME CONCRETELY.  [probe_var_leaf] inducts on the
   parallel src/img wf_args (c0 order), reaches the direct-var leaf, and makes
   BOTH c0-tail wf_substs explicit:
       Htsub_src : wf_subst l c' (with_names_from cA' rest) cA'   (over c')
       Htsub_img : wf_subst l c  (with_names_from cA' rest[/s/]) cA' (over c)
   These ARE the user's "complete c0-prefix wf_substs, for free"
   (wf_subst_from_wf_args on the tail).

   RESULT (mechanically verified): the c0-prefix substitution does NOT close
   the leaf.  After aligning the image head sort to t1[/s/] (the use-sort image,
   via the faithful_sort_align identity [Himgsort], REAL proof), the residual is
       eq_sort l c (t1[/s/]) (t'[/s/])
   transported from the SOURCE use=declared equation (via term_sorts_eq)
       Heqsrc : eq_sort l c' t1 t'      (t1 = the c0-telescoped USE sort,
                                          t' = the DECLARED Cfull sort)
   and this transport is [covering_var_leaf_transport] = [eq_sort_subst] needing
       eq_subst l c c' s s   =   the COMPLETE wf_subst l c s c'  (over Cfull=c').
   The c0-tail substitutions [Htsub_src]/[Htsub_img] are over cA' (the OPERATOR
   ctx), NOT over c' (=Cfull); they substitute t1's INTERNAL telescoping
   (tnm[/wnf cA' rest/]) but the use<->declared link [Heqsrc] is an equation
   OVER c' whose transport by s is irreducibly the full eq_subst over c'.

   WHY c0-order does not help (re-derived for the BASE var too): even the
   c0-LAST/closed arg (use-sort closed, e.g. T_a) has a DECLARED Cfull sort t'
   that can mention arbitrary OTHER Cfull vars; transporting eq_sort l c' t' T_a
   by s still needs the full eq_subst over c'.  The dependency the frame relies
   on ("declared sort telescopes in c0 order") is an eq_sort fact OVER c', not a
   syntactic containment, so it cannot be discharged with a proper sub-subst.

   NET: the single [admit] below is EXACTLY [wf_subst l c s c'] (the full subst),
   the SAME wall as Core.wf_subst_from_args_image's Hself and
   CtxReadback.skip_var_decl_sort_core's residual.  The c0-order frame
   sharpens WHERE the transport lives (it is the use<->declared eq over c',
   not the use-sort's internal telescoping) but does not break it.
   (Earlier-session note: the skip guard is [inb x (fv e1)] -- ANY occurring
   var, so a syntactic use=declared escape is unavailable; conversions are
   genuinely in play.)
   ===================================================================== *)
Set Implicit Arguments.

Require Import Lists.List.
Import ListNotations.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core ModelImpls.
From Pyrosome.Theory Require WfCutElim.
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

  Section __.
    Context (l:lang)
      (Hwfl : wf_lang l).

  (* ---------------------------------------------------------------------
     THE CORE QUESTION, stated as a lemma over c0.

     We have a direct variable arg [x] occupying some slot in c0.  We want its
     image [sg x] wf at its DECLARED Cfull sort [t'_x][/s/].

     The c0-order induction: induct on the IMAGE wf_args (over c0).  At each
     step the head's use-sort is instantiated by the c0-TAIL args, for which
     we have BOTH a source wf_args and an image wf_args (= a complete sub
     wf_subst over the c0-tail, via wf_subst_from_wf_args).

     I want to see EXACTLY what is available at the var leaf and whether the
     c0-prefix (tail) substitution closes the use->declared transport.
     --------------------------------------------------------------------- *)

  (* First, the parallel source/image wf_args over c0, plus the source typing of
     each ARG VARIABLE at its DECLARED Cfull sort.  This is the data the engine /
     wf_subst_from_args_image have.  We package the per-var declared-sort link as
     a hypothesis [Hdecl] giving, for each direct-var arg, its Cfull declared sort
     and the source eq between use and declared (= what term_sorts_eq provides). *)

  Lemma probe_var_leaf c' c s cA args
    : wf_ctx l c' ->
      wf_ctx l cA ->
      wf_args l c' args cA ->
      map fst s = map fst c' ->
      wf_args l c args[/s/] cA ->
      forall x t',
        In (x, t') c' ->
        (* x occurs as a DIRECT arg at some slot of [args] *)
        In (var x) args ->
        wf_term l c (subst_lookup s x) t'[/s/].
  Proof.
    intros Hwfc HwfcA Hsrc Hmap Himg x t' Hin Hocc.
    (* Induct on the SOURCE wf_args; the image telescopes in parallel. *)
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
    (* Now in scope:
       head src: wf_term l c' e0 (tnm[/wnf cA' rest/])
       tail src: wf_args l c' rest cA'
       head img: wf_term l c (e0[/s/]) (tnm[/wnf cA' rest[/s/]/])
       tail img: wf_args l c (rest[/s/]) cA'
       The TAIL gives, via wf_subst_from_wf_args, a complete wf_subst over cA'
       in BOTH c' and c. *)
    cbn [In] in Hocc.
    destruct Hocc as [Hhead | Htail].
    2:{ (* x occurs in the tail -- recurse, the tail is itself a parallel
           src/img wf_args over cA'. *)
      eapply IHargs; [ exact HwfcA' | eassumption | eassumption | exact Htail ]. }
    (* x is THIS arg: e0 = var x. *)
    subst e0.
    (* The c0-TAIL wf_subst, both sides: *)
    match goal with
    | Hs : wf_args l c' rest cA' |- _ =>
        pose proof (wf_subst_from_wf_args (Model:=core_model l) Hs) as Htsub_src
    end.
    match goal with
    | Hs : wf_args l c (map (term_subst s) rest) cA' |- _ =>
        pose proof (wf_subst_from_wf_args (Model:=core_model l) Hs) as Htsub_img
    end.
    (* head img typing: *)
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
      by (eapply (term_sorts_eq (l:=l)); [ exact Hwfl | exact Hwfc | exact Hsrch | exact Hvar ]).
    assert (Hlen : length cA' = length rest)
      by (eapply wf_args_length_eq; eassumption).
    assert (Hwst1 : ws_sort (map fst cA') tnm).
    { pose proof (wf_lang_implies_ws_noext Hwfl) as Hwsl.
      eapply (wf_sort_implies_ws (V_Eqb_ok:=V_Eqb_ok)); [ exact Hwsl | exact Hwst_tnm ]. }
    assert (Himgsort : (t1[/s/]) = (tnm[/with_names_from cA' (map (term_subst s) rest)/])).
    { subst t1.
      change (map (term_subst s) rest) with (rest[/s/]).
      rewrite with_names_from_args_subst.
      erewrite subst_assoc; [ reflexivity | typeclasses eauto | ].
      rewrite map_fst_with_names_from by exact Hlen. exact Hwst1. }
    eapply wf_term_conv; [ exact Himgh |].
    (* GOAL: eq_sort l c (tnm[/θ_img/]) (t'[/s/]) = eq_sort l c (t1[/s/]) (t'[/s/])
       Heqsrc : eq_sort l c' t1 t'.   Closes ONLY with full wf_subst l c s c'. *)
    assert (Hg : eq_sort l c (t1[/s/]) (t'[/s/]))
      by (eapply covering_var_leaf_transport;
          [ exact Hwfl | exact Hwfc | exact Hmap
          | (* WALL: wf_subst l c s c' *) admit | exact Heqsrc ]).
    rewrite Himgsort in Hg. exact Hg.
  Admitted.  (* SINGLE admit = wf_subst l c s c' (the full subst). See header. *)

  End __.
End WithVar.
