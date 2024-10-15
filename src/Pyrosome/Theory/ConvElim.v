
Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core CutFreeInd ModelImpls.


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

  
  Section WithLangAndCtx.
    Context (l : lang)
      (wfl : wf_lang l)
      (c : ctx)
      (wfc : wf_ctx (Model:= core_model l) c).

    Local Notation eq_sort := (eq_sort l c).
    Local Notation core_eq_subst := (eq_subst (Model:= core_model l) c).
    Local Notation core_eq_args := (eq_args (Model:= core_model l) c).

    Inductive eq_term : sort -> term -> term -> Prop :=
    | eq_term_by : forall name c' t e1 e2 s1 s2 t',
        In (name,term_eq_rule c' e1 e2 t) l ->
        eq_subst c' s1 s2 ->
        eq_sort t[/s2/] t' ->
        eq_term t' e1[/s1/] e2[/s2/]
    | eq_term_cong : forall name c' args t s1 s2 t',
        In (name,term_rule c' args t) l ->
        eq_args c' s1 s2 ->
        eq_sort t[/(with_names_from c' s2)/] t' ->
        eq_term t' (con name s1) (con name s2)
    | eq_term_var : forall n t t',
        In (n, t) c ->
        eq_sort t t' ->
        eq_term t' (var n) (var n)
    | eq_term_trans : forall t e1 e12 e2,
        eq_term t e1 e12 ->
        eq_term t e12 e2 ->
        eq_term t e1 e2
    | eq_term_sym : forall t e1 e2, eq_term t e1 e2 -> eq_term t e2 e1
  with eq_subst : ctx -> subst -> subst -> Prop :=
  | eq_subst_nil : eq_subst [] [] []
  | eq_subst_cons : forall (c' : ctx) (s1 s2 : subst),
                    eq_subst c' s1 s2 ->
                    forall (name : V) (t : sort) (e1 e2 : term),
                    eq_term t [/s2 /] e1 e2 ->
                    eq_subst ((name, t) :: c') ((name, e1) :: s1)
                      ((name, e2) :: s2)
  with eq_args : ctx -> list term -> list term -> Prop :=
  | eq_args_nil : eq_args [] [] []
  | eq_args_cons : forall (c' : ctx) (es1 es2 : list term),
      eq_args c' es1 es2 ->
      forall (name : V) (t : sort) (e1 e2 : term),
        eq_term t [/with_names_from c' es2 /] e1 e2 ->
        eq_args ((name, t) :: c') (e1 :: es1) (e2 :: es2).

  Scheme eq_term_ind' := Minimality for eq_term Sort Prop
      with eq_subst_ind' := Minimality for eq_subst Sort Prop
      with eq_args_ind' := Minimality for eq_args Sort Prop.

  
  Combined Scheme eq_ind
    from eq_term_ind', eq_subst_ind', eq_args_ind'.

    
  Local Hint Constructors eq_term eq_args eq_subst : lang_core.

  Lemma eq_term_conv e1 e2 t t'
    : eq_term t e1 e2 ->
      eq_sort t t' ->
      eq_term t' e1 e2.
  Proof.
    induction 1;
      basic_goal_prep; eauto.
    all: [> eapply eq_term_by
         | eapply eq_term_cong
         | eapply eq_term_var
         | eapply eq_term_trans
         | eapply eq_term_sym];
      eauto using eq_sort_trans.
  Qed.

  Hint Resolve core_model_ok : lang_core.

  
  (*TODO: move to Model.v*)
  Lemma eq_args_implies_wf_r c' s1 s2
    : Model.eq_args (Model:= core_model l) c c' s1 s2 -> wf_args (Model:= core_model l) c s2 c'.
  Proof.
    induction 1;
      basic_goal_prep;
      basic_core_crush.
    eapply eq_term_wf_r; eauto.
  Qed.
  Hint Resolve eq_args_implies_wf_r : lang_core.


  Local Lemma eq_implies_core
    : (forall t e1 e2, eq_term t e1 e2 -> Core.eq_term l c t e1 e2)
      /\ (forall c' s1 s2, eq_subst c' s1 s2 -> Model.eq_subst (Model:= core_model l) c c' s1 s2)
      /\ (forall c' s1 s2, eq_args c' s1 s2 -> Model.eq_args (Model:= core_model l) c c' s1 s2).
  Proof.
    eapply eq_ind;
      basic_goal_prep;
      eauto using  Core.eq_term_sym, Core.eq_term_trans with lang_core.
    use_rule_in_wf.
    eapply Core.eq_term_conv; eauto.
    eapply term_con_congruence; eauto.
  Qed.

  
  Local Lemma core_implies_eq
    : (forall t1 t2, Core.eq_sort l c t1 t2 -> True)
      /\ (forall t e1 e2, Core.eq_term l c t e1 e2 -> eq_term t e1 e2)
      /\ (forall c' s1 s2, Model.eq_subst (Model:= core_model l) c c' s1 s2 -> eq_subst c' s1 s2)
      /\ (forall c' s1 s2, Model.eq_args (Model:= core_model l) c c' s1 s2 -> eq_args c' s1 s2).
  Proof.
    eapply cut_ind;
      basic_goal_prep;
      try use_rule_in_wf;
      eauto using eq_term_sym, eq_term_trans, eq_term_conv with lang_core.
    {
      eapply eq_term_by; eauto.
      basic_core_crush.
    }
    {
      eapply eq_term_cong; eauto.
      autorewrite with lang_core utils in *.
      break.
      eapply eq_sort_subst; eauto with lang_core.
      eapply eq_args_implies_eq_subst.
      eapply Model.eq_args_refl; eauto with lang_core.
    }
  Qed.
    
  Lemma eq_term_iff t e1 e2
    : eq_term t e1 e2 <-> Core.eq_term l c t e1 e2.
  Proof.
    split; [ eapply eq_implies_core; eauto
           | eapply core_implies_eq; eauto].
  Qed.

      Section ConvInd.
      
      Context (P_term : sort -> term -> term -> Prop)
        (P_subst : ctx -> subst -> subst -> Prop)
        (* TODO: question: define in terms of P_subst? *)
        (P_args : ctx -> list term -> list term -> Prop).

      
    
    (* Term hypotheses *)
    Context (f : forall (c' : ctx) (name : V) (t : sort) (e1 e2 : term) s1 s2 t',
                In (name, term_eq_rule c' e1 e2 t) l ->
                core_eq_subst c' s1 s2 ->
                P_subst c' s1 s2 ->
                eq_sort t [/s2 /] t' -> 
                P_term t' e1[/s1/] e2[/s2/])
      (f0 : forall (c' : ctx) (name : V) (t : sort) args s1 s2 t',
          In (name, term_rule c' args t) l ->
          core_eq_args c' s1 s2 ->
          P_args c' s1 s2 ->
          eq_sort t [/(with_names_from c' s2)/] t' ->
          P_term t' (con name s1) (con name s2))
      (f01 : forall (n : V) (t : sort) t',
          eq_sort t t' -> 
          In (n, t) c -> P_term t' (var n) (var n))
      (f1 : forall (t : sort) (e1 e12 e2 : term),
          Core.eq_term l c t e1 e12 -> P_term t e1 e12 ->
          Core.eq_term l c t e12 e2 -> P_term t e12 e2 ->
          P_term t e1 e2)
      (f2 : forall (t : sort) (e1 e2 : term),
          Core.eq_term l c t e1 e2 -> P_term t e1 e2 -> P_term t e2 e1).

      (* subst hypotheses *)
      Context (f4 : P_subst [] [] [])
        (f5 : forall (c' : ctx) s1 s2,
            core_eq_subst c' s1 s2 ->
            P_subst c' s1 s2 ->
            forall (name : V) (t : sort) (e1 e2 : term),
              Core.eq_term l c t [/s2/] e1 e2 ->
              P_term t [/s2/] e1 e2 ->
              P_subst ((name, t) :: c') ((name,e1) :: s1) ((name,e2) :: s2)).
      
      (* args hypotheses *)
      Context (f6 : P_args [] [] [])
        (f7 : forall (c' : ctx) s1 s2,
            core_eq_args c' s1 s2 ->
            P_args c' s1 s2 ->
            forall (name : V) (t : sort) (e1 e2 : term),
              Core.eq_term l c t [/with_names_from c' s2/] e1 e2 ->
              P_term t [/with_names_from c' s2/] e1 e2 ->
              P_args ((name, t) :: c') (e1 :: s1) (e2 :: s2)).
      
      Theorem conv_ind
        : (forall s t t0, Core.eq_term l c s t t0 -> P_term s t t0) /\
          (forall c0 s s0, core_eq_subst c0 s s0 -> P_subst c0 s s0) /\
          (forall c0 s s0, core_eq_args c0 s s0 -> P_args c0 s s0).
      Proof.
        enough ((forall s t t0, eq_term s t t0 -> P_term s t t0) /\
                  (forall c0 s s0, eq_subst c0 s s0 -> P_subst c0 s s0) /\
                  (forall c0 s s0, eq_args c0 s s0 -> P_args c0 s s0)) as HC.
        {
          revert V_Eqb_ok V_default wfl wfc HC; clear.
          intros V_Eqb_ok V_default wfl wfc HC.
          destruct HC as  [H_term [H_subst H_args]].
          split; [intros; eapply H_term; eapply core_implies_eq; eauto|].
          split; [intros; eapply H_subst; eapply core_implies_eq; eauto|].
          intros; eapply H_args; eapply core_implies_eq; eauto.
        }
        eapply eq_ind; intros.
        all: [> eapply f
             | eapply f0
             | eapply f01
             | eapply f1
             | eapply f2
             | eapply f4
             | eapply f5
             | eapply f6
             | eapply f7];
          eauto.
        all: eapply eq_implies_core; eauto.
      Qed.

    End ConvInd.

  Section TermConvInd.
    
    Context (P_term : sort -> term -> term -> Prop).

    Fixpoint P_args c s1 s2 :=
      match c, s1, s2 with
      | [], [], [] => True
      | (n,t)::c', e1::s1, e2::s2 =>
          P_args c' s1 s2
          /\ P_term t[/with_names_from c' s2/] e1 e2
      | _, _, _ => False
      end.
    
    Fixpoint P_subst c s1 s2 :=
      match c, s1, s2 with
      | [], [], [] => True
      | (n,t)::c', (n1,e1)::s1, (n2,e2)::s2 =>
          n1 = n
          /\ n2 = n
          /\ P_subst c' s1 s2
          /\ P_term t[/s2/] e1 e2
      | _, _, _ => False
      end.
    
    (* Term hypotheses *)
    Context (f : forall (c' : ctx) (name : V) (t : sort) (e1 e2 : term) s1 s2 t',
                In (name, term_eq_rule c' e1 e2 t) l ->
                core_eq_subst c' s1 s2 ->
                P_subst c' s1 s2 ->
                eq_sort t [/s2 /] t' -> 
                P_term t' e1[/s1/] e2[/s2/])
      (f0 : forall (c' : ctx) (name : V) (t : sort) args s1 s2 t',
          In (name, term_rule c' args t) l ->
          core_eq_args c' s1 s2 ->
          P_args c' s1 s2 ->
          eq_sort t [/(with_names_from c' s2)/] t' ->
          P_term t' (con name s1) (con name s2))
      (f01 : forall (n : V) (t : sort) t',
          eq_sort t t' -> 
          In (n, t) c -> P_term t' (var n) (var n))
      (f1 : forall (t : sort) (e1 e12 e2 : term),
          Core.eq_term l c t e1 e12 -> P_term t e1 e12 ->
          Core.eq_term l c t e12 e2 -> P_term t e12 e2 ->
          P_term t e1 e2)
      (f2 : forall (t : sort) (e1 e2 : term),
          Core.eq_term l c t e1 e2 -> P_term t e1 e2 -> P_term t e2 e1).

    Lemma term_conv_ind s t t0 : Core.eq_term l c s t t0 -> P_term s t t0.
    Proof.
      enough ((forall s t t0, Core.eq_term l c s t t0 -> P_term s t t0) /\
                (forall c0 s s0, core_eq_subst c0 s s0 -> P_subst c0 s s0) /\
                (forall c0 s s0, core_eq_args c0 s s0 -> P_args c0 s s0)) by firstorder.
      eapply conv_ind;
        eauto;
        try constructor; eauto using eq_term_sym, eq_term_trans, eq_term_conv with lang_core.
      all: basic_goal_prep.
    Qed.

  End TermConvInd.

  End WithLangAndCtx.
  
End WithVar.

