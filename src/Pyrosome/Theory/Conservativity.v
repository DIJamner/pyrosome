From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require CutElim.
From Pyrosome.Theory Require Import Core CutFreeInd.


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

  Definition sort_name (t : sort) : V := match t with scon n _ => n end.

  Definition ctx_in_stratum (P : V -> bool) (c : ctx) : bool :=
    forallb (fun p => P (sort_name (snd p))) c.

  Lemma sort_name_subst (s : subst) (t : sort)
    : sort_name t[/s/] = sort_name t.
  Proof. destruct t; reflexivity. Qed.

  Lemma ctx_in_stratum_cons P n t (c : ctx)
    : ctx_in_stratum P ((n,t)::c)
      = (P (sort_name t) && ctx_in_stratum P c)%bool.
  Proof. reflexivity. Qed.

  Section Conservativity.
    Context (l l' : lang) (wfl : wf_lang l) (wfl' : wf_lang l') (P : V -> bool).

    Hypothesis Hsort_rule : forall n c' args,
        In (n, sort_rule c' args) l ->
        In (n, sort_rule c' args) l' /\ ctx_in_stratum P c' = true.
    Hypothesis Hsort_eq : forall n c' t1 t2,
        In (n, sort_eq_rule c' t1 t2) l ->
        In (n, sort_eq_rule c' t1 t2) l' /\ ctx_in_stratum P c' = true
        /\ P (sort_name t1) = P (sort_name t2).
    Hypothesis Hterm_rule : forall n c' args t,
        In (n, term_rule c' args t) l -> P (sort_name t) = true ->
        In (n, term_rule c' args t) l' /\ ctx_in_stratum P c' = true.
    Hypothesis Hterm_eq : forall n c' e1 e2 t,
        In (n, term_eq_rule c' e1 e2 t) l -> P (sort_name t) = true ->
        In (n, term_eq_rule c' e1 e2 t) l' /\ ctx_in_stratum P c' = true.

    Section WithCtx.
      Context (c : ctx)
        (wfc : wf_ctx (Model:=core_model l) c)
        (wfc' : wf_ctx (Model:=core_model l') c).

      Let P_sort t1 t2 :=
            CutElim.eq_sort V l' c t1 t2 /\ P (sort_name t1) = P (sort_name t2).
      Let P_term t e1 e2 :=
            P (sort_name t) = true -> CutElim.eq_term V l' c t e1 e2.
      Let P_subst c' s1 s2 :=
            ctx_in_stratum P c' = true -> CutElim.eq_subst V l' c c' s1 s2.
      Let P_args c' s1 s2 :=
            ctx_in_stratum P c' = true -> CutElim.eq_args V l' c c' s1 s2.

      Lemma conservative_cut
        : (forall t1 t2, eq_sort l c t1 t2 -> P_sort t1 t2)
          /\ (forall t e1 e2, eq_term l c t e1 e2 -> P_term t e1 e2)
          /\ (forall c' s1 s2,
                 eq_subst (Model:=core_model l) c c' s1 s2 -> P_subst c' s1 s2)
          /\ (forall c' s1 s2,
                 eq_args (Model:=core_model l) c c' s1 s2 -> P_args c' s1 s2).
      Proof.
        apply (cut_ind V l wfl c wfc P_sort P_term P_subst P_args);
          unfold P_sort, P_term, P_subst, P_args in *;
          clear P_sort P_term P_subst P_args.
        (* Hsort0 : sort_eq_by *)
        {
          intros c' name t1 t2 s1 s2 Hin Hsub IH.
          pose proof (Hsort_eq _ _ _ _ Hin) as [Hin' [Hstrat Hhead]].
          split.
          { eapply CutElim.eq_sort_by; eauto. }
          { rewrite !sort_name_subst; auto. }
        }
        (* Hsort1 : sort_cong *)
        {
          intros c' name args s1 s2 Hin Hargs IH.
          pose proof (Hsort_rule _ _ _ Hin) as [Hin' Hstrat].
          split.
          { eapply CutElim.eq_sort_cong; eauto. }
          { reflexivity. }
        }
        (* Hsort2 : trans *)
        {
          intros t1 t12 t2 _ [H1 E1] _ [H2 E2].
          split; [eapply CutElim.eq_sort_trans; eauto | congruence].
        }
        (* Hsort3 : sym *)
        {
          intros t1 t2 _ [H1 E1].
          split; [eapply CutElim.eq_sort_sym; eauto | congruence].
        }
        (* f : term_eq_by *)
        {
          intros c' name t e1 e2 s1 s2 Hin Hsub IH Hp.
          rewrite sort_name_subst in Hp.
          pose proof (Hterm_eq _ _ _ _ _ Hin Hp) as [Hin' Hstrat].
          eapply CutElim.eq_term_by; eauto.
        }
        (* f0 : term_cong *)
        {
          intros c' name t args s1 s2 Hin Hargs IH Hp.
          rewrite sort_name_subst in Hp.
          pose proof (Hterm_rule _ _ _ _ Hin Hp) as [Hin' Hstrat].
          eapply CutElim.eq_term_cong; eauto.
        }
        (* f01 : var *)
        {
          intros n t Hin _.
          eapply CutElim.eq_term_var; eauto.
        }
        (* f1 : trans *)
        {
          intros t e1 e12 e2 _ IH1 _ IH2 Hp.
          eapply CutElim.eq_term_trans; eauto.
        }
        (* f2 : sym *)
        {
          intros t e1 e2 _ IH Hp.
          eapply CutElim.eq_term_sym; eauto.
        }
        (* f3 : conv *)
        {
          intros t t' _ [Hs E] e1 e2 _ IH Hp.
          eapply CutElim.eq_term_conv; [ eapply IH; congruence | eauto ].
        }
        (* f4 : subst nil *)
        {
          intros _; constructor.
        }
        (* f5 : subst cons *)
        {
          intros c' s1 s2 _ IH name t e1 e2 _ IHt Hstrat.
          rewrite ctx_in_stratum_cons in Hstrat.
          apply Bool.andb_true_iff in Hstrat as [Ht Hc'].
          constructor; eauto.
          apply IHt; rewrite sort_name_subst; auto.
        }
        (* f6 : args nil *)
        {
          intros _; constructor.
        }
        (* f7 : args cons *)
        {
          intros c' s1 s2 _ IH name t e1 e2 _ IHt Hstrat.
          rewrite ctx_in_stratum_cons in Hstrat.
          apply Bool.andb_true_iff in Hstrat as [Ht Hc'].
          constructor; eauto.
          apply IHt; rewrite sort_name_subst; auto.
        }
      Qed.

    End WithCtx.

    Theorem eq_conservative (c : ctx)
      (wfc : wf_ctx (Model:=core_model l) c)
      (wfc' : wf_ctx (Model:=core_model l') c)
      : (forall t1 t2, eq_sort l c t1 t2 -> eq_sort l' c t1 t2)
        /\ (forall t e1 e2, eq_term l c t e1 e2 -> P (sort_name t) = true ->
                            eq_term l' c t e1 e2).
    Proof.
      pose proof (conservative_cut c wfc) as [Hs [Ht _]].
      pose proof (core_iff_cut V l' wfl' c wfc') as [Cs [Ct _]].
      split.
      - intros t1 t2 H; apply Cs; apply Hs; auto.
      - intros t e1 e2 H Hp; apply Ct; apply Ht; auto.
    Qed.

  End Conservativity.

  Definition rule_conservative (P : V -> bool) (l' : lang) (p : V * rule) : bool :=
    let (n, r) := p in
    match r with
    | sort_rule c' _ => (inb (n,r) l' && ctx_in_stratum P c')%bool
    | sort_eq_rule c' t1 t2 =>
        (inb (n,r) l' && ctx_in_stratum P c'
         && eqb (P (sort_name t1)) (P (sort_name t2)))%bool
    | term_rule c' _ t =>
        if P (sort_name t) then (inb (n,r) l' && ctx_in_stratum P c')%bool else true
    | term_eq_rule c' _ _ t =>
        if P (sort_name t) then (inb (n,r) l' && ctx_in_stratum P c')%bool else true
    end.

  Definition lang_conservative P (l l' : lang) : bool :=
    forallb (rule_conservative P l') l.

  Lemma inb_true_In (x : V * rule) (L : lang)
    : inb x L = true -> In x L.
  Proof.
    intro H.
    apply (proj1 (inb_is_In x L)).
    rewrite H; exact I.
  Qed.

  Theorem eq_conservative_check (l l' : lang) (wfl : wf_lang l) (wfl' : wf_lang l')
    (P : V -> bool)
    : lang_conservative P l l' = true ->
      forall c, wf_ctx (Model:=core_model l) c -> wf_ctx (Model:=core_model l') c ->
      (forall t1 t2, eq_sort l c t1 t2 -> eq_sort l' c t1 t2)
      /\ (forall t e1 e2, eq_term l c t e1 e2 -> P (sort_name t) = true ->
                          eq_term l' c t e1 e2).
  Proof.
    unfold lang_conservative.
    intro Hall.
    rewrite forallb_forall in Hall.
    apply eq_conservative; auto.
    - intros n c' args Hin.
      specialize (Hall _ Hin); cbn in Hall.
      apply Bool.andb_true_iff in Hall as [H1 H2].
      split; auto using inb_true_In.
    - intros n c' t1 t2 Hin.
      specialize (Hall _ Hin); cbn in Hall.
      apply Bool.andb_true_iff in Hall as [Hall H3].
      apply Bool.andb_true_iff in Hall as [H1 H2].
      split; [auto using inb_true_In|].
      split; auto.
      destruct (P (sort_name t1)), (P (sort_name t2));
        cbn in H3; congruence.
    - intros n c' args t Hin Hp.
      specialize (Hall _ Hin); cbn in Hall.
      rewrite Hp in Hall.
      apply Bool.andb_true_iff in Hall as [H1 H2].
      split; auto using inb_true_In.
    - intros n c' e1 e2 t Hin Hp.
      specialize (Hall _ Hin); cbn in Hall.
      rewrite Hp in Hall.
      apply Bool.andb_true_iff in Hall as [H1 H2].
      split; auto using inb_true_In.
  Qed.

End WithVar.
