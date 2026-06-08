(* =====================================================================
   SESSION 18 (2026-06-08): substitution-typing-reflection metatheorem,
   mechanized to a SINGLE isolated obstruction.

   [wf_term_fv] proves the reflection lemma by mutual term/args induction
   ([WfCutElim.wf_cut_ind]) with the image hypothesis stated at the SOURCE
   CANONICAL sort [sort_of c0 e2].  This single design choice DISSOLVES the
   two sub-obstructions that blocked the WIP [wf_term_fv'] attempt:
     - CONVERSION case: trivial, because the canonical-sort hypothesis does
       not mention the term's (conv-varying) sort -- [P e t] and [P e t']
       are literally the same proposition.
     - n-ary STRENGTHENING: never needed; no s/c splitting.
   FIVE of the six cases are real, admit-free proof: con, var leaf, conv,
   args-nil, args-cons-tail, and -- crucially -- the args-cons NESTED-CON
   head (closed by re-canonicalizing the image via [canonical_sort] +
   [sort_of_con_subst], NO eq_sort transport).

   The SINGLE remaining [admit] is the DIRECT-VARIABLE-ARGUMENT leaf:
       have  Hwfe2 : wf_term l c (s2 xv) (USE-sort[/s2/])
       goal  wf_term l c (s2 xv) (DECLARED-sort[/s2/])
   bridging needs eq_sort l c (use[/s2/]) (decl[/s2/]) = [eq_sort_subst] of
   the source equation [eq_sort l c0 use decl] (from [term_sorts_eq]) by s2,
   which requires [eq_subst l c c0 s2 s2] = the COMPLETE [wf_subst l c s2 c0]
   being constructed.  This is the IDENTICAL wall as [Core.wf_subst_from_
   args_image]'s [Hself] and [CtxReadback.skip_var_decl_sort_core]'s residual.
   The re-canonicalization trick that closes the nested-con head does NOT
   apply to a bare var (no con structure to commute the substitution through).

   NOTE this file is WIP scratch (not built by make); it imports only built
   Theory files and compiles standalone with `coqc` + the 4 -R mappings.
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

  Section __.
    Context (l:lang)
      (Hwfl : wf_lang l).

  Lemma wf_term_inv_up_to_conv c e t
    : wf_ctx l c ->
      wf_term l c e t ->
      (exists n s c' args t', e = (Term.con n s)
                            /\ In (n, term_rule c' args t') l
                            /\ Core.eq_sort l c t t' [/with_names_from c' s /]
                            /\ wf_args l c s c')
      \/ (exists x t', e = Term.var x /\ In (x,t') c /\ Core.eq_sort l c t t').
  Proof.
    induction 2.
    {
      left; repeat eexists; eauto.
      eapply eq_sort_refl.
      eapply rule_in_wf in H0; eauto; safe_invert H0.
      basic_core_crush.
    }
    {
      destruct (IHwf_term ltac:(assumption)); break; subst;
        [left | right];
        repeat eexists; eauto.
      2:{ eauto using eq_sort_trans, eq_sort_sym. }
      eapply eq_sort_trans; eauto using eq_sort_trans, eq_sort_sym.
    }
    {
      right; repeat eexists; eauto.
      basic_core_crush.
    }
  Qed.

  (*TODO: move somewhere else*)
  Definition sort_of c e :=
    match e with
    | Term.var x => unwrap_with_default (named_list_lookup_err c x)
    | Term.con n s =>
        match named_list_lookup_err l n with
          | Some (term_rule c' _ t) => t[/with_names_from c' s/]
          | Some (term_eq_rule c' _ _ t) => t[/with_names_from c' s/]
        | _ => default
        end
    end.

  Lemma canonical_sort c e t
    : all_fresh c ->
      Core.wf_term l c e t ->
      Core.wf_term l c e (sort_of c e).
  Proof.
    intro Hfresh.
    revert e t.
    apply WfCutElim.wf_term_cut_ind;
      basic_goal_prep; auto.
    {
      pose proof H as H'.
      rewrite <- all_fresh_named_list_lookup_err_in in H
          by (try typeclasses eauto; basic_core_crush).
      rewrite <- H.
      clear H.
      eapply wf_term_by; eauto.
    }
    {
      pose proof H as H'.
      rewrite <- all_fresh_named_list_lookup_err_in in H
          by (try typeclasses eauto; basic_core_crush).
      rewrite <- H.
      clear H. cbn.
      eapply wf_term_var; eauto.
    }
  Qed.

  Lemma named_list_lookup_in A s x e (d:A)
    : all_fresh s -> In (x,e) s -> named_list_lookup d s x = e.
  Proof.
    induction s;
      basic_goal_prep;
      basic_utils_crush.
    eqb_case x v;
      basic_utils_crush.
  Qed.

  Lemma In_flat_map {A B} x (f : A -> _ B) lst
    : In x (flat_map f lst) <-> exists a, In a lst /\ In x (f a).
  Proof.
    induction lst;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  (* [sort_of] of a [con] commutes with substitution. *)
  Lemma sort_of_con_subst c0 s2 n s
    : wf_lang l ->
      wf_ctx l c0 ->
      wf_term l c0 (con n s) (sort_of c0 (con n s)) ->
      (sort_of c0 (con n s))[/s2/] = sort_of c0 ((con n s)[/s2/]).
  Proof.
    intros Hwfl' Hwfc0 Hwf.
    apply WfCutElim.invert_wf_term_con in Hwf.
    destruct Hwf as (c' & args & t' & Hin & Hwfargs & _).
    assert (Hwsl : ws_lang l) by (apply (@wf_lang_implies_ws_noext V _ V_Eqb_ok); exact Hwfl').
    assert (Hws : ws_sort (map fst c') t').
    { eapply (wf_sort_implies_ws (V_Eqb_ok:=V_Eqb_ok));
        [ exact Hwsl
        | eapply term_rule_in_sort_wf; [ exact Hwfl' | exact Hin ] ]. }
    assert (Hlen : length c' = length s) by (eapply wf_args_length_eq; eassumption).
    cbn [sort_of].
    rewrite <- all_fresh_named_list_lookup_err_in in Hin
      by (try typeclasses eauto; exact (wf_lang_ext_all_fresh Hwfl')).
    rewrite <- Hin.
    cbn [apply_subst term_substable].
    change ((con n s)[/s2/]) with (con n s[/s2/]).
    cbn [sort_of].
    rewrite <- Hin.
    (* goal: t'[/wnf c' s/][/s2/] = t'[/wnf c' (s[/s2/])/] *)
    rewrite with_names_from_args_subst.
    erewrite subst_assoc; [ reflexivity | typeclasses eauto | ].
    rewrite map_fst_with_names_from by exact Hlen.
    exact Hws.
  Qed.

  (* The reflection lemma: from the source typing of [e2] and the typing of its
     image under [s2], each variable occurring in [e2] has its value wf at its
     substituted declared sort.  The image hypothesis is stated at the SOURCE
     canonical sort [sort_of c0 e2], which is invariant under conversion and
     commutes with substitution at [con] nodes -- this trivializes both the
     conversion case and the var leaf. *)
  Lemma wf_term_fv c c0 s2
    : wf_lang l ->
      wf_ctx l c ->
      wf_ctx l c0 ->
      all_fresh s2 ->
      map fst s2 = map fst c0 ->
      forall e2 t,
      wf_term l c0 e2 t ->
      wf_term l c e2 [/s2 /] (sort_of c0 e2)[/s2/] ->
      forall n e t', In n (fv e2) ->
                  In (n,e) s2 ->
                  In (n,t') c0 ->
                  wf_term l c e t'[/s2/].
  Proof.
    intros Hwfl' Hwfcc Hwfc0 Hfrs2 Hmap e2 t Hwf.
    revert e2 t Hwf.
    pose proof (@WfCutElim.wf_cut_ind V _ l c0
      (fun e2 t =>
        wf_term l c e2[/s2/] (sort_of c0 e2)[/s2/] ->
        forall n e t', In n (fv e2) -> In (n,e) s2 -> In (n,t') c0 ->
                       wf_term l c e t'[/s2/])
      (fun s_a c_a =>
        wf_args l c (s_a[/s2/]) c_a ->
        forall n e t', In n (flat_map (fv (V:=V)) s_a) -> In (n,e) s2 -> In (n,t') c0 ->
                       wf_term l c e t'[/s2/])) as Hind.
    refine (proj1 (Hind _ _ _ _ _)).
    { (* H1: con case *)
      intros name c' args t s Hin Hwfargs IH Himg.
      intros n e t' Hfv Hins2 Hinc0.
      cbn [fv] in Hfv. unfold fv_args in IH.
      (* invert the image to get the args image wf at op-telescope sorts *)
      assert (Hcanon : sort_of c0 (con name s) = t[/with_names_from c' s/]).
      { cbn [sort_of].
        rewrite <- all_fresh_named_list_lookup_err_in in Hin
          by (try typeclasses eauto; exact (wf_lang_ext_all_fresh Hwfl')).
        rewrite <- Hin. reflexivity. }
      rewrite Hcanon in Himg.
      change ((con name s)[/s2/]) with (con name s[/s2/]) in Himg.
      apply WfCutElim.invert_wf_term_con in Himg.
      destruct Himg as (c'' & args'' & t'' & Hin'' & Hwfargs'' & _).
      pose proof (in_all_fresh_same _ _ _ _ (wf_lang_ext_all_fresh Hwfl') Hin'' Hin) as Heq.
      safe_invert Heq.
      eapply IH; eauto.
    }
    { (* H2: var case -- TRIVIAL: source canonical sort = declared sort *)
      intros n0 t0 Hin0 Himg.
      intros n e t' Hfv Hins2 Hinc0.
      cbn [fv] in Hfv. destruct Hfv as [Hfv|[]]; subst n.
      assert (t' = t0).
      { eapply in_all_fresh_same; [ eapply wf_ctx_all_fresh; exact Hwfc0 | exact Hinc0 | exact Hin0 ]. }
      subst t0.
      assert (e = subst_lookup s2 n0).
      { symmetry. eapply named_list_lookup_in; eauto. }
      subst e.
      assert (Hlk : Some t' = named_list_lookup_err c0 n0).
      { eapply all_fresh_named_list_lookup_err_in;
          [ try typeclasses eauto | eapply wf_ctx_all_fresh; exact Hwfc0 | exact Hin0 ]. }
      cbn [sort_of apply_subst term_substable term_subst] in Himg.
      rewrite <- Hlk in Himg. cbn [unwrap_with_default] in Himg.
      change (term_var_map (term_subst_lookup s2) (var n0)) with (subst_lookup s2 n0) in Himg.
      exact Himg.
    }
    { (* H3: conv case -- trivial, predicate's hypothesis (canonical sort)
            doesn't mention t *)
      intros e t0 t' Hwfe IH Heqs Himg. apply IH. exact Himg.
    }
    { (* H4: args nil *)
      intros Himg n e t' Hfv; cbn in Hfv; contradiction.
    }
    { (* H5: args cons *)
      intros c' es Hwfargs IHargs name t e Hwfe IHe Himg.
      intros n ev t' Hfv Hins2 Hinc0.
      cbn [apply_subst substable_args args_subst map] in Himg.
      safe_invert Himg.
      match goal with
      | Ht : Model.wf_term c (term_subst s2 e) _ |- _ => rename Ht into Hwfe2
      end.
      match goal with
      | Ha : Model.wf_args c (map (term_subst s2) es) c' |- _ => rename Ha into Hwfargs2
      end.
      cbn [flat_map] in Hfv. apply in_app_or in Hfv.
      destruct Hfv as [Hfv_e | Hfv_es].
      2:{ eapply IHargs; [ exact Hwfargs2 | exact Hfv_es | exact Hins2 | exact Hinc0 ]. }
      (* Hwfe2 : wf_term l c (e[/s2/]) (t[/wnf c' (es[/s2/])/]) -- head at use-sort.
         Recurse into head via IHe at e's source canonical sort. *)
      destruct e as [xv | ne se].
      - (* DIRECT VAR ARG: e = var xv.  fv (var xv) = {xv}, so n = xv. *)
        cbn [fv] in Hfv_e. destruct Hfv_e as [Hfv_e|[]]; subst n.
        (* goal: wf_term l c ev (t'[/s2/]); Hwfe2: value at use-sort. WALL. *)
        admit.
      - (* NESTED CON ARG: re-canonicalize via canonical_sort + sort_of_con_subst. *)
        eapply IHe; [ | exact Hfv_e | exact Hins2 | exact Hinc0 ].
        (* GOAL: wf_term l c (con ne se)[/s2/] (sort_of c0 (con ne se))[/s2/] *)
        pose proof (canonical_sort (c:=c) (e:=(con ne se)[/s2/]) (t:=t[/with_names_from c' (map (term_subst s2) es)/])) as Hcan.
        change ((con ne se)[/s2/]) with (con ne se[/s2/]) in Hcan |- *.
        specialize (Hcan ltac:(eapply wf_ctx_all_fresh; exact Hwfcc) Hwfe2).
        erewrite sort_of_con_subst with (c0:=c0) (s2:=s2) (n:=ne) (s:=se).
        4:{ eapply canonical_sort; [ eapply wf_ctx_all_fresh; exact Hwfc0 | exact Hwfe ]. }
        2: exact Hwfl'.
        2: exact Hwfc0.
        exact Hcan.
    }
    Unshelve.
    all: shelve.
  Admitted.

  End __.

End WithVar.
