Set Implicit Arguments.

Set Default Proof Mode "Classic".

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core ClosedTerm CutFreeInd.
(* TODO: theory depending on tools? *)
From Pyrosome.Tools Require Import AllConstructors.

Module Notations.
  Export ClosedTerm.Notations.
End Notations.
Import Notations.

Section WithVar.
  Context (V : Type)
    {V_Eqb : Eqb V}
    {V_Eqb_ok : Eqb_ok V_Eqb}
    {V_default : WithDefault V}.

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  Notation term := (@term V).
  Notation con := (@con V).
  Notation ctx := (@ctx V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).

  Section TermsAndRules.
  Context (l : lang).

  (* TODO: two separate versions. Which is the source of truth? *)
  Definition vtr : _ -> Term.term V := term_var_map (fun n => Term.con n []).
  Definition svtr (t : Term.sort V) :=
    let (n,s) := t in
    scon n (map vtr s).
  
  Fixpoint term_vtr (e : Term.term V) : term :=
    match e with
    | Term.var n => con n []
    | Term.con n l => con n (map term_vtr l)
    end.
  
  Definition sort_vtr (t : Term.sort V) : term :=
    let (n,s) := t in
    con n (map term_vtr s).

  (*TODO: move to ClosedTerm.v*)
  Fixpoint unclose (e : term) : Term.term V :=
    let (n,s) := e in
    Term.con n (map unclose s).
  
  Definition unclose_sort (e : term) : Term.sort V :=
    let (n,s) := e in
    Term.scon n (map unclose s).

  Definition sort_to_var_rule (t : Term.sort V) : rule :=
    term_rule [] [] (svtr t).
  
  Definition ctx_to_rules : ctx -> lang :=
    named_map sort_to_var_rule.

  (*TODO: move to utils*)
  Lemma lookup_named_map {A B C} `{Eqb A}
    n (s : @NamedList.named_list A B) (f : B -> C) b
    : (*In n (map fst s) ->*)
      f (named_list_lookup b s n)
      = named_list_lookup (f b) (NamedList.named_map f s) n.
  Proof.
    induction s;
      basic_goal_prep;
      try case_match;
      basic_utils_crush.
  Qed.
  
  Lemma named_list_lookup_change_default {A B} `{Eqb_ok A}
    n (s : @NamedList.named_list A B) d1 d2
    : In n (map fst s) ->
      named_list_lookup d1 s n
      = named_list_lookup d2 s n.
  Proof.
    induction s;
      basic_goal_prep; 
      basic_utils_crush.
    rewrite H1.
    reflexivity.
  Qed.
  
  Lemma map_fst_named_map A B C `{Eqb A}
    (s : @NamedList.named_list A B) (f : B -> C)
    : map fst (NamedList.named_map f s) = map fst s.
  Proof.
    induction s;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  Hint Rewrite map_fst_named_map : utils.
  
  Lemma term_vtr_subst e s
    : well_scoped (map fst s) e ->
      (vtr e[/s/])
      = e[/named_map vtr s/].
  Proof.
    induction e;
      basic_goal_prep;
      basic_term_crush.
    {
      unfold subst_lookup.
      rewrite lookup_named_map with (f:= vtr).
      apply named_list_lookup_change_default.
      basic_utils_crush.
    }
    {
      unfold vtr in *.
      basic_goal_prep.
      rewrite map_map.
      generalize dependent l0;
        induction l0;
        basic_goal_prep;
        basic_term_crush.
    }
  Qed.

  
  Lemma args_vtr_subst e s
    : well_scoped (map fst s) e ->
      (map vtr e[/s/])
      = e[/named_map vtr s/].
  Proof.
    unfold vtr in *.
    induction e;
      basic_goal_prep;
      basic_term_crush.
    eapply term_vtr_subst; eauto.
  Qed.
    
  Lemma sort_vtr_subst t s
    : well_scoped (map fst s) t ->
      (svtr t[/s/])
      = t[/named_map vtr s/].
  Proof.
    destruct t;
      basic_goal_prep;
      basic_term_crush.
    eapply args_vtr_subst; eauto.
  Qed.

  
  Lemma in_ctx_to_rules n t c
    : In (n,t) c ->
      In (n, term_rule [] [] (svtr t)) (ctx_to_rules c).
  Proof.
    unfold ctx_to_rules, sort_to_var_rule.
    induction c;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  Context (wfl : wf_lang l).

  Section WithCtx.
    Context (c : ctx)
      (wfc : wf_ctx (Model:= core_model l) c).
    Let l' := (ctx_to_rules c) ++ l.
    
    Context (wfl' : wf_lang l').

    Lemma eq_vtr
      : (forall t t0 : sort V, eq_sort l c t t0 ->
                               eq_sort l' [] (svtr t) (svtr t0)) /\
          (forall (s : sort V) (t t0 : Term.term V),
              eq_term l c s t t0 ->
              eq_term l' [] (svtr s) (vtr t) (vtr t0)) /\
          (forall (c0 : Term.ctx V) (s s0 : Term.subst V),
              Model.eq_subst (Model:= core_model l) c c0 s s0 ->
              wf_ctx (Model:= core_model l) c0 ->
              Model.eq_subst (Model:= core_model l') [] c0
                (named_map vtr s)
                (named_map vtr s0)) /\
          (forall (c0 : Term.ctx V) (s s0 : list (Term.term V)),
              Model.eq_args (Model:= core_model l) c c0 s s0 ->
              wf_ctx (Model:= core_model l) c0 ->
              Model.eq_args (Model:= core_model l') [] c0
                (map vtr s)
                (map vtr s0)).
    Proof.
      eapply cut_ind;
        try typeclasses eauto;
        eauto using eq_sort_trans, eq_sort_sym, eq_term_trans;
        basic_goal_prep.
      {
        use_rule_in_wf.
        basic_core_crush.
        rewrite !sort_vtr_subst;
          basic_core_crush.
        eapply eq_sort_subst; eauto.
        2: eapply wf_ctx_lang_monotonicity; eauto.
        2: subst l'; basic_utils_crush.
        eapply eq_sort_lang_monotonicity with (l:=l).
        1:subst l'; basic_utils_crush.
        basic_core_crush.
      }
      {
        use_rule_in_wf.
        autorewrite with utils lang_core term in *; break.
        eapply sort_con_congruence; eauto.
        subst l'; basic_utils_crush.
      }
      {
        use_rule_in_wf.
        basic_core_crush.
        rewrite !sort_vtr_subst, !term_vtr_subst by basic_core_crush.
        eapply eq_term_subst; eauto.
        2: eapply wf_ctx_lang_monotonicity; eauto.
        2: subst l'; basic_utils_crush.
        eapply eq_term_lang_monotonicity with (l:=l).
        1:subst l'; basic_utils_crush.
        basic_core_crush.
      }
      {
        use_rule_in_wf.
        autorewrite with utils lang_core term in *; break.
        eapply term_con_congruence; eauto.
        1:subst l'; basic_utils_crush.
        {
          right.
          rewrite sort_vtr_subst by basic_core_crush.
          f_equal.
          rewrite with_names_from_map_is_named_map.
          reflexivity.
        }
      }
      {
        unfold vtr.
        cbn.
        eapply eq_term_refl.
        replace (svtr t) with (svtr t)[/with_names_from ([] : ctx) []/]
        by eauto using sort_subst_nil.
        eapply wf_term_by; eauto with lang_core.
        subst l'; basic_utils_crush; left.
        eapply in_ctx_to_rules; eauto.
      }
      {
        eapply eq_term_sym.
        eauto.
      }
      {
        eapply eq_term_conv; eauto.
      }
      { constructor. }
      {
        basic_core_crush.
        rewrite <- sort_vtr_subst; eauto.
        erewrite eq_subst_dom_eq_r; eauto with lang_core.
      }
      { constructor. }
      {
        basic_core_crush.
        rewrite with_names_from_map_is_named_map.
        rewrite <- sort_vtr_subst; eauto.
        basic_core_crush.
      }
    Qed.

    Fixpoint rtv (e : Term.term V) :=
      match e with
      | var _ => default (* never happens *)
      | Term.con n s =>
          if inb n (map fst c) then var n
          else Term.con n (map rtv s)
      end.

    Definition srtv (t : sort V) :=
      let (n,s) := t in
      scon n (map rtv s).

  Lemma term_rtv_subst e s
    : well_scoped (map fst s) e ->
      all (fun x => fresh x l) (map fst c) ->
      all_constructors (fun n => In n (map fst l)) e ->
      (rtv e[/s/])
      = e[/named_map rtv s/].
  Proof.
    induction e;
      basic_goal_prep;
      basic_term_crush.
    {
      unfold subst_lookup.
      rewrite lookup_named_map with (f:= rtv).
      apply named_list_lookup_change_default.
      basic_utils_crush.
    }
    {
      case_match;
        basic_term_crush.
      {
        assert (fresh n l).
        {
          eapply in_all in H1; eauto.
        }
        eapply H2; eauto.
      }
      {
        rewrite map_map.
        generalize dependent l0;
          induction l0;
          basic_goal_prep;
          basic_term_crush.
      }
    }
  Qed.

  
  Lemma args_rtv_subst e s
    : well_scoped (map fst s) e ->
      all (fun x => fresh x l) (map fst c) ->
      all (all_constructors (fun n => In n (map fst l))) e ->
      (map rtv e[/s/])
      = e[/named_map rtv s/].
  Proof.
    induction e;
      basic_goal_prep;
      basic_term_crush.
    eapply term_rtv_subst; eauto.
  Qed.
    
  Lemma sort_rtv_subst t s
    : well_scoped (map fst s) t ->
      all (fun x => fresh x l) (map fst c) ->
      all_constructors_sort (fun n => In n (map fst l)) t ->
      (srtv t[/s/])
      = t[/named_map rtv s/].
  Proof.
    destruct t;
      basic_goal_prep;
      basic_term_crush.
    eapply args_rtv_subst; eauto.
  Qed.

  (* Round-trip: [rtv] (con->var) inverts [vtr] (var->con) on terms whose
     variables live in [c] and whose constructors avoid [c]. *)
  Lemma rtv_vtr (e : Term.term V)
    : all_constructors (fun n => fresh n c) e ->
      well_scoped (map fst c) e ->
      rtv (vtr e) = e.
  Proof.
    induction e; basic_goal_prep.
    { case_match; basic_utils_crush. }
    { case_match; basic_goal_prep.
      { basic_utils_crush. }
      { f_equal. rewrite map_map.
        revert H H1; induction l0; basic_goal_prep; basic_utils_crush. } }
  Qed.

  Lemma srtv_svtr (t : sort V)
    : all_constructors_sort (fun n => fresh n c) t ->
      well_scoped (map fst c) t ->
      srtv (svtr t) = t.
  Proof.
    destruct t; basic_goal_prep.
    f_equal.
    rewrite map_map.
    revert H H0; induction l0; basic_goal_prep; basic_utils_crush.
    apply rtv_vtr; auto.
  Qed.

  (* Reverse of [in_ctx_to_rules]: every rule in [ctx_to_rules c0] is a
     constant term rule arising from some context entry. *)
  Lemma in_ctx_to_rules_inv (c0 : ctx) n r
    : In (n, r) (ctx_to_rules c0) -> exists t, r = sort_to_var_rule t /\ In (n, t) c0.
  Proof.
    unfold ctx_to_rules.
    induction c0; basic_goal_prep; basic_utils_crush.
  Qed.

  Context (H_c_disjoint : all (fun x : V => fresh x l) (map fst c)).
    Lemma eq_rtv
      : (forall t t0 : sort V, eq_sort l' [] t t0 ->
                               eq_sort l c (srtv t) (srtv t0)) /\
          (forall (s : sort V) (t t0 : Term.term V),
              eq_term l' [] s t t0 ->
              eq_term l c (srtv s) (rtv t) (rtv t0)) /\
          (forall (c0 : Term.ctx V) (s s0 : Term.subst V),
              Model.eq_subst (Model:= core_model l') [] c0 s s0 ->
              wf_ctx (Model:= core_model l) c0 ->
              Model.eq_subst (Model:= core_model l) c c0
                (named_map rtv s)
                (named_map rtv s0)) /\
          (forall (c0 : Term.ctx V) (s s0 : list (Term.term V)),
              Model.eq_args (Model:= core_model l') [] c0 s s0 ->
              wf_ctx (Model:= core_model l) c0 ->
              Model.eq_args (Model:= core_model l) c c0
                (map rtv s)
                (map rtv s0)).
    Proof.
      (* Reverse of [eq_vtr]: a closed equality over [l' = ctx_to_rules c ++ l]
         maps back to an open equality over [l] in context [c], with [rtv]/[srtv]
         turning the closing constants back into variables.  Unlike the forward
         direction, the rule cases must split on whether a rule comes from [l]
         (standard) or from [ctx_to_rules c] (a context variable: the [term_rule]
         congruence case below). *)
      eapply cut_ind;
        try typeclasses eauto;
        eauto using eq_sort_trans, eq_sort_sym, eq_term_sym, eq_term_trans
        with lang_core.
      (* var case is vacuous: the closed context is empty. *)
      5: (intros n t Hin; inversion Hin).
      (* sort_eq_rule (necessarily from [l]) *)
      1: (intros c' name t1 t2 s1 s2 Hin Hsub IHsub;
          apply in_app_or in Hin; destruct Hin as [Hin|Hin];
          [ apply in_ctx_to_rules_inv in Hin; break; discriminate | ];
          use_rule_in_wf;
          autorewrite with utils lang_core term in *;
          break;
          pose proof (wf_lang_implies_ws_noext wfl) as Hwsl;
          assert (E1 : srtv t1[/s1/] = t1[/named_map rtv s1/]) by
            (apply sort_rtv_subst;
             [ rewrite (eq_subst_dom_eq_l Hsub); eapply wf_sort_implies_ws; eauto
             | exact H_c_disjoint
             | eapply wf_sort_all_constructors; eauto ]);
          assert (E2 : srtv t2[/s2/] = t2[/named_map rtv s2/]) by
            (apply sort_rtv_subst;
             [ rewrite (eq_subst_dom_eq_r Hsub); eapply wf_sort_implies_ws; eauto
             | exact H_c_disjoint
             | eapply wf_sort_all_constructors; eauto ]);
          rewrite E1, E2;
          eapply eq_sort_subst; [eapply eq_sort_by; exact Hin | apply IHsub; exact H | exact H]).
      (* sort_rule congruence (necessarily from [l]) *)
      1: (intros c' name args s1 s2 Hin Hargs IHargs;
          apply in_app_or in Hin; destruct Hin as [Hin|Hin];
          [ apply in_ctx_to_rules_inv in Hin; break; discriminate | ];
          cbn [srtv];
          use_rule_in_wf;
          autorewrite with utils lang_core term in *;
          break;
          eapply sort_con_congruence; eauto; apply IHargs; assumption).
      (* term_eq_rule (necessarily from [l]) *)
      1: (intros c' name t e1 e2 s1 s2 Hin Hsub IHsub;
          apply in_app_or in Hin; destruct Hin as [Hin|Hin];
          [ apply in_ctx_to_rules_inv in Hin; break; discriminate | ];
          use_rule_in_wf;
          autorewrite with utils lang_core term in *;
          break;
          pose proof (wf_lang_implies_ws_noext wfl) as Hwsl;
          assert (Et : srtv t[/s2/] = t[/named_map rtv s2/]) by
            (apply sort_rtv_subst; [ rewrite (eq_subst_dom_eq_r Hsub); eapply wf_sort_implies_ws; eauto | exact H_c_disjoint | eapply wf_sort_all_constructors; eauto ]);
          assert (Ee1 : rtv e1[/s1/] = e1[/named_map rtv s1/]) by
            (apply term_rtv_subst; [ rewrite (eq_subst_dom_eq_l Hsub); eapply wf_term_implies_ws; eauto | exact H_c_disjoint | eapply wf_term_all_constructors; eauto ]);
          assert (Ee2 : rtv e2[/s2/] = e2[/named_map rtv s2/]) by
            (apply term_rtv_subst; [ rewrite (eq_subst_dom_eq_r Hsub); eapply wf_term_implies_ws; eauto | exact H_c_disjoint | eapply wf_term_all_constructors; eauto ]);
          rewrite Et, Ee1, Ee2;
          eapply eq_term_subst; [eapply eq_term_by; exact Hin | apply IHsub; exact H | exact H]).
      (* eq_subst cons *)
      2: (intros c' s1 s2 Hsub IHsub name t e1 e2 Heqt IHterm Hwfc';
          autorewrite with utils lang_core model in Hwfc'; break;
          pose proof (wf_lang_implies_ws_noext wfl) as Hwsl;
          assert (Et : srtv t[/s2/] = t[/named_map rtv s2/]) by
            (apply sort_rtv_subst; [ rewrite (eq_subst_dom_eq_r Hsub); eapply wf_sort_implies_ws; eauto | exact H_c_disjoint | eapply wf_sort_all_constructors; eauto ]);
          rewrite Et in IHterm).
      2: (cbn [NamedList.named_map]; apply eq_subst_cons; [apply IHsub; exact H0 | exact IHterm]).
      (* eq_args cons *)
      2: (intros c' s1 s2 Hargs IHargs name t e1 e2 Heqt IHterm Hwfc';
          autorewrite with utils lang_core model in Hwfc'; break;
          pose proof (wf_lang_implies_ws_noext wfl) as Hwsl).
      2: (assert (Et : srtv (t[/with_names_from c' s2/]) = t[/with_names_from c' (map rtv s2)/]) by (rewrite sort_rtv_subst; [ rewrite with_names_from_map_is_named_map; reflexivity | erewrite map_fst_with_names_from by (eauto using eq_args_length_eq_r); eapply wf_sort_implies_ws; eauto | exact H_c_disjoint | eapply wf_sort_all_constructors; eauto ]); rewrite Et in IHterm; cbn [map]; apply eq_args_cons; [apply IHargs; exact H0 | exact IHterm]).
      (* term_rule congruence: splits on rule source ([ctx_to_rules c] vs [l]) *)
      1: (intros c' name t args s1 s2 Hin Hargs IHargs;
          apply in_app_or in Hin; destruct Hin as [Hin|Hin]).
      (* sub-case A: rule from [ctx_to_rules c], i.e. [name] is a context variable *)
      1: (apply in_ctx_to_rules_inv in Hin; destruct Hin as [tx [Heq Hintx]]; unfold sort_to_var_rule in Heq; inversion Heq; subst; inversion Hargs; subst; assert (Hwfsx : wf_sort l c tx) by (eapply in_ctx_wf; eauto); assert (Hrt : srtv (svtr tx) = tx) by (apply srtv_svtr; [ apply (@all_constructors_sort_weaken V V_Eqb V_default (fun n => In n (map fst l)) (fun n => fresh n c) tx); [ intros n Hnl Hnc; exact (in_all (fun x => fresh x l) (map fst c) n H_c_disjoint Hnc Hnl) | exact (wf_sort_all_constructors Hwfsx) ] | exact (wf_sort_implies_ws (wf_lang_implies_ws_noext wfl) Hwfsx) ]); assert (Hrtvar : rtv (Term.con name []) = var name) by (change (Term.con name []) with (vtr (var name)); apply rtv_vtr; [ exact I | cbn; eapply pair_fst_in; exact Hintx ]); cbn [with_names_from]; rewrite sort_subst_nil, Hrt, Hrtvar; apply eq_term_refl; apply wf_term_var; exact Hintx).
      (* sub-case B: rule from [l], standard congruence *)
      1: (use_rule_in_wf; autorewrite with utils lang_core term in *; break;
          pose proof (wf_lang_implies_ws_noext wfl) as Hwsl;
          assert (Hin_l : In name (map fst l)) by (eapply pair_fst_in; exact Hin);
          assert (Hfn : fresh name c) by (intro Hnc; exact (in_all (fun x => fresh x l) (map fst c) name H_c_disjoint Hnc Hin_l))).
      1: (assert (Hrtv1 : rtv (Term.con name s1) = Term.con name (map rtv s1)) by (cbn [rtv]; case_match; basic_utils_crush); assert (Hrtv2 : rtv (Term.con name s2) = Term.con name (map rtv s2)) by (cbn [rtv]; case_match; basic_utils_crush); assert (Et : srtv (t[/with_names_from c' s2/]) = t[/with_names_from c' (map rtv s2)/]) by (rewrite sort_rtv_subst; [ rewrite with_names_from_map_is_named_map; reflexivity | erewrite map_fst_with_names_from by (eapply eq_args_length_eq_r; exact Hargs); exact (wf_sort_implies_ws (wf_lang_implies_ws_noext wfl) H1) | exact H_c_disjoint | exact (wf_sort_all_constructors H1) ]); rewrite Hrtv1, Hrtv2, Et; eapply term_con_congruence; [ exact Hin | right; reflexivity | exact wfl | apply IHargs; exact H ]).
    Qed.
      
  (*
  Lemma term_vars_as_rules_wf c e t
    : Core.wf_term l c e t ->
      Core.wf_term (ctx_to_rules c ++ l) [] (unclose (term_vars_as_rules e))
        (unclose_sort (sort_vars_as_rules t)).
  Proof.
    induction 1;
      basic_goal_prep;
      basic_core_crush.
    {
      admit (*TODO: mutualize*).
    }
    {
      eapply wf_term_conv; eauto.
      (*TODO: eq first*)
      admit.
    }
    {
      remember (unclose_sort _) as ct.
      replace ct with ct[/with_names_from ([] : ctx) []/]
        by eauto using sort_subst_nil.
      eapply wf_term_by; eauto with lang_core.
      Lemma in_sort_vars_as_rules
        basic_utils_crush.
  
  Lemma ctx_to_rules_wf c
    : wf_ctx (Model:= core_model l) c ->
      all (fun x => fresh x l) (map fst c) ->
      wf_lang_ext l (ctx_to_rules c).
  Proof.
    unfold ctx_to_rules, sort_to_var_rule, unclose_sort.
    induction 1;
      basic_goal_prep;
      basic_core_crush.
    destruct v; basic_goal_prep.
    TODO: need lemma about wf_sort


   *)

  End WithCtx.
  End TermsAndRules.

  (* [ctx_to_rules c] is a well-formed extension of [l]: each context
     entry [(x,t)] becomes a constant term rule [term_rule [] [] (svtr t)],
     whose result sort is well-formed because [eq_vtr] (via reflexivity)
     closes [wf_sort l c t] into [wf_sort (ctx_to_rules c ++ l) [] (svtr t)].
     The [wfl'] hypothesis [eq_vtr] needs is supplied inductively by the IH. *)
  Lemma ctx_to_rules_wf (l : lang)
    : wf_lang l ->
      forall (c : ctx),
      wf_ctx (Model:= core_model l) c ->
      all (fun x => fresh x l) (map fst c) ->
      wf_lang_ext l (ctx_to_rules c).
  Proof.
    intros wfl c.
    induction c as [| [v s] c IH]; basic_goal_prep.
    1: constructor.
    break.
    autorewrite with utils lang_core model in H.
    break.
    specialize (IH H2 H1).
    pose proof (wf_lang_concat wfl IH) as Hwfl'.
    apply wf_lang_cons.
    2: exact IH.
    1:{ unfold fresh, ctx_to_rules in *.
        rewrite map_app, map_fst_named_map, in_app_iff.
        1: tauto.
        exact V_Eqb. }
    unfold sort_to_var_rule.
    apply wf_term_rule.
    1: constructor.
    2: constructor.
    pose proof (eq_vtr wfl H2 Hwfl') as Hev.
    destruct Hev as [Hes _].
    pose proof (Hes s s (eq_sort_refl H3)) as Heqs.
    eapply eq_sort_wf_l; eauto; constructor.
  Qed.

  (* Forward closing of [wf_term]: derived from [eq_vtr] applied to the
     reflexive equality of [e].  [wfl'] (= [wf_lang (ctx_to_rules c ++ l)])
     comes from [ctx_to_rules_wf]. *)
  Lemma wf_term_vtr (l : lang) (c : ctx)
    : wf_lang l -> wf_ctx (Model:=core_model l) c ->
      all (fun x => fresh x l) (map fst c) ->
      forall (e : Term.term V) (t : sort V),
      wf_term l c e t -> wf_term (ctx_to_rules c ++ l) [] (vtr e) (svtr t).
  Proof.
    intros wfl wfc Hdisj e t Hwf.
    pose proof (wf_lang_concat wfl (ctx_to_rules_wf wfl wfc Hdisj)) as Hwfl'.
    destruct (eq_vtr wfl wfc Hwfl') as [_ [Het _]].
    pose proof (Het t e e (eq_term_refl Hwf)) as Heq.
    eapply eq_term_wf_l; eauto; constructor.
  Qed.

  (* Round-trip under well-formedness: [rtv]/[srtv] invert [vtr]/[svtr] on
     terms/sorts well-formed in [c] over [l] (with [c] disjoint from [l]).
     Discharges [rtv_vtr]/[srtv_svtr]'s side conditions from [wf_*]. *)
  Lemma rtv_vtr_wf (l : lang) (c : ctx)
    : wf_lang l -> wf_ctx (Model:=core_model l) c ->
      all (fun x => fresh x l) (map fst c) ->
      forall (e : Term.term V) (t : sort V),
      wf_term l c e t -> rtv c (vtr e) = e.
  Proof.
    intros wfl wfc Hdisj e t Hwf.
    apply rtv_vtr.
    - apply (@all_constructors_term_weaken V V_Eqb V_default
               (fun n => In n (map fst l)) (fun n => fresh n c) e);
        [ intros n Hnl Hnc; exact (in_all (fun x => fresh x l) (map fst c) n Hdisj Hnc Hnl)
        | exact (wf_term_all_constructors Hwf) ].
    - exact (wf_term_implies_ws (wf_lang_implies_ws_noext wfl) Hwf).
  Qed.

  Lemma srtv_svtr_wf (l : lang) (c : ctx)
    : wf_lang l -> wf_ctx (Model:=core_model l) c ->
      all (fun x => fresh x l) (map fst c) ->
      forall (t : sort V),
      wf_sort l c t -> srtv c (svtr t) = t.
  Proof.
    intros wfl wfc Hdisj t Hwf.
    apply srtv_svtr;
      [ apply (@all_constructors_sort_weaken V V_Eqb V_default
                 (fun n => In n (map fst l)) (fun n => fresh n c) t);
          [ intros n Hnl Hnc; exact (in_all (fun x => fresh x l) (map fst c) n Hdisj Hnc Hnl)
          | exact (wf_sort_all_constructors Hwf) ]
      | exact (wf_sort_implies_ws (wf_lang_implies_ws_noext wfl) Hwf) ].
  Qed.

End WithVar.
