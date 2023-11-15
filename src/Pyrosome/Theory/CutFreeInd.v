
Require Import String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require CutElim.
From Pyrosome.Theory Require Import Core.



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

    Local Notation eq_subst := (eq_subst (Model:= core_model l) c).
    Local Notation eq_args := (eq_args (Model:= core_model l) c).

    
    (*TODO: move to CutElim.v*)
    Local Lemma eq_args_iff_cut
      : forall c' s1 s2,
        CutElim.eq_args _ l c c' s1 s2 <->
          eq_args c' s1 s2.
    Proof.
      split; induction 1;
        basic_goal_prep;
        constructor; eauto.
      all: [> eapply CutElim.cut_implies_core
           | eapply CutElim.core_implies_cut];
        eauto.
      eapply CutElim.wf_lang_iff_cut; eauto.
    Qed.
    
    Lemma core_iff_cut
      : (forall t1 t2,
            CutElim.eq_sort _ l c t1 t2 <->
              eq_sort l c t1 t2)
        /\ (forall t e1 e2,
               CutElim.eq_term _ l c t e1 e2 <->
                 eq_term l c t e1 e2)
        /\ (forall c' s1 s2,
               CutElim.eq_subst _ l c c' s1 s2 <->
                 eq_subst c' s1 s2)
        /\ (forall c' s1 s2,
               CutElim.eq_args _ l c c' s1 s2 <->
                 eq_args c' s1 s2).
    Proof using V_Eqb_ok V_default wfl wfc.
      intuition;
        try (eapply CutElim.core_implies_cut
             || eapply CutElim.cut_implies_core
             || eapply eq_args_iff_cut);
        eauto.
      all: eapply CutElim.wf_lang_iff_cut; eauto.
    Qed.
    
    Section CutInd.
      
      Context (P_sort : sort -> sort -> Prop)
        (P_term : sort -> term -> term -> Prop)
        (P_subst : ctx -> subst -> subst -> Prop)
        (* TODO: question: define in terms of P_subst? *)
        (P_args : ctx -> list term -> list term -> Prop).

      (* sort hypotheses *)
      Context (Hsort0 : forall (c' : ctx) (name : V) t1 t2 s1 s2,
                  In (name, sort_eq_rule c' t1 t2) l ->
                  eq_subst c' s1 s2 ->
                  P_subst c' s1 s2 ->
                  P_sort t1[/s1/] t2[/s2/])
        (Hsort1 : forall (c' : ctx) (name : V) args s1 s2,
            In (name, sort_rule c' args) l ->
            eq_args c' s1 s2 ->
            P_args c' s1 s2 ->
            P_sort (scon name s1) (scon name s2))
        (Hsort2 : forall (t1 t12 t2 : sort),
            eq_sort l c t1 t12 -> P_sort t1 t12 ->
            eq_sort l c t12 t2 -> P_sort t12 t2 ->
            P_sort t1 t2)
        (Hsort3 : forall (t1 t2 : sort),
            eq_sort l c t1 t2 -> P_sort t1 t2 -> P_sort t2 t1).
      
      (* Term hypotheses *)
      Context (f : forall (c' : ctx) (name : V) (t : sort) (e1 e2 : term) s1 s2,
                  In (name, term_eq_rule c' e1 e2 t) l ->
                  eq_subst c' s1 s2 ->
                  P_subst c' s1 s2 ->
                  P_term t[/s2/] e1[/s1/] e2[/s2/])
        (f0 : forall (c' : ctx) (name : V) (t : sort) args s1 s2,
            In (name, term_rule c' args t) l ->
            eq_args c' s1 s2 ->
            P_args c' s1 s2 ->
            P_term t[/(with_names_from c' s2)/] (con name s1) (con name s2))
        (f01 : forall (n : V) (t : sort),
            In (n, t) c -> P_term t (var n) (var n))
        (f1 : forall (t : sort) (e1 e12 e2 : term),
            eq_term l c t e1 e12 -> P_term t e1 e12 ->
            eq_term l c t e12 e2 -> P_term t e12 e2 ->
            P_term t e1 e2)
        (f2 : forall (t : sort) (e1 e2 : term),
            eq_term l c t e1 e2 -> P_term t e1 e2 -> P_term t e2 e1)
        (f3 : forall (t t' : sort),
            eq_sort l c t t' -> P_sort t t' ->
            forall e1 e2 : term,
              eq_term l c t e1 e2 -> P_term t e1 e2 -> P_term t' e1 e2).

      (* subst hypotheses *)
      Context (f4 : P_subst [] [] [])
        (f5 : forall (c' : ctx) s1 s2,
            eq_subst c' s1 s2 ->
            P_subst c' s1 s2 ->
            forall (name : V) (t : sort) (e1 e2 : term),
              eq_term l c t [/s2/] e1 e2 ->
              P_term t [/s2/] e1 e2 ->
              P_subst ((name, t) :: c') ((name,e1) :: s1) ((name,e2) :: s2)).
      
      (* args hypotheses *)
      Context (f6 : P_args [] [] [])
        (f7 : forall (c' : ctx) s1 s2,
            eq_args c' s1 s2 ->
            P_args c' s1 s2 ->
            forall (name : V) (t : sort) (e1 e2 : term),
              eq_term l c t [/with_names_from c' s2/] e1 e2 ->
              P_term t [/with_names_from c' s2/] e1 e2 ->
              P_args ((name, t) :: c') (e1 :: s1) (e2 :: s2)).
      
      Theorem cut_ind
        : (forall t t0, eq_sort l c t t0 -> P_sort t t0) /\
            (forall s t t0, eq_term l c s t t0 -> P_term s t t0) /\
            (forall c0 s s0, eq_subst c0 s s0 -> P_subst c0 s s0) /\
            (forall c0 s s0, eq_args c0 s s0 -> P_args c0 s s0).
      Proof.
        enough ((forall t t0, CutElim.eq_sort _ l c t t0 -> P_sort t t0) /\
                  (forall s t t0, CutElim.eq_term _ l c s t t0 -> P_term s t t0) /\
                  (forall c0 s s0, CutElim.eq_subst _ l c c0 s s0 -> P_subst c0 s s0) /\
                  (forall c0 s s0, CutElim.eq_args _ l c c0 s s0 -> P_args c0 s s0)) as HCE.
        {
          revert V_Eqb_ok V_default wfl wfc HCE; clear.
          intros V_Eqb_ok V_default wfl wfc HCE.
          destruct HCE as [H_sort [H_term [H_subst H_args]]].
          split; [intros; eapply H_sort; eapply core_iff_cut; eauto|].
          split; [intros; eapply H_term; eapply core_iff_cut; eauto|].
          split; [intros; eapply H_subst; eapply core_iff_cut; eauto|].
          intros; eapply H_args; eapply core_iff_cut; eauto.
        }
        eapply CutElim.cut_ind; intros.
        all: [> eapply Hsort0
             | eapply Hsort1
             | eapply Hsort2
             | eapply Hsort3
             | eapply f
             | eapply f0
             | eapply f01
             | eapply f1
             | eapply f2
             | eapply f3
             | eapply f4
             | eapply f5
             | eapply f6
             | eapply f7];
          eauto.
        all: eapply core_iff_cut; eauto.
      Qed.

    End CutInd.

  End WithLangAndCtx.
  
End WithVar.
