Set Implicit Arguments.

Require Import Ltac2.Ltac2.
Set Default Proof Mode "Classic".

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils SymmetricInduction.
From Pyrosome.Theory Require Import Core ClosedTerm CutFreeInd.

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
      revert dependent l0;
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

    (* TODO: theory depending on tools? *)
    Require Import Tools.AllConstructors.
    
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
        revert dependent l0;
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
      eapply cut_ind;
        try typeclasses eauto;
        eauto using eq_sort_trans, eq_sort_sym, eq_term_sym, eq_term_trans
        with lang_core;
        basic_goal_prep.
      {
        use_rule_in_wf.
        basic_core_crush.
        rewrite !sort_rtv_subst; eauto.
        (*TODO: need all_constructors wf; currently in compilers.
        Note: might be worth refactoring compilers using cutfreeind
        all_constructors_sort
        Lemma sort_constr
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
    Qed.*)
    Abort.
      
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
End WithVar.
