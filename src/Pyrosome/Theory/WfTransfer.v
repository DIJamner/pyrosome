From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core WfCutElim CutFreeInd.
From Pyrosome.Theory Require Conservativity.

(* Generic transfer of well-formed terms from a language [l'] down into a
   sublanguage [l], when every con-node occurring in the term is named by a
   rule that either (a) is excluded (e.g. handled specially, as [typerec] is
   in TyperecPartialEval.v) or (b) already belongs to [l], and sort equality
   at the empty context/[] transfers from [l'] down to [l].

   This generalizes TyperecPartialEval.v's [no_typerec_transfer]. *)

Section WithVar.
  Context (V : Type)
    {V_Eqb : Eqb V}
    {V_Eqb_ok : Eqb_ok V_Eqb}
    {V_default : WithDefault V}.

  Notation named_list := (@named_list V).
  Notation term := (@term V).
  Notation var := (@var V).
  Notation con := (@con V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).

  (* every con node of [e] is named outside [excluded] *)
  Fixpoint avoids (excluded : list V) (e : term) : bool :=
    match e with
    | Term.var _ => true
    | Term.con n s => (negb (inb n excluded) && forallb (avoids excluded) s)%bool
    end.

  Lemma avoids_unfold excluded n s
    : avoids excluded (Term.con n s)
      = (negb (inb n excluded) && forallb (avoids excluded) s)%bool.
  Proof. reflexivity. Qed.

  (* every term rule of [l'] whose name is not excluded is a rule of [l] *)
  Definition term_rules_covered (excluded : list V) (l l' : lang) : bool :=
    forallb (fun p =>
               match snd p with
               | term_rule _ _ _ => (inb (fst p) excluded || inb p l)%bool
               | _ => true
               end) l'.

  Section Transfer.
    Context (l l' : lang) (excluded : list V)
      (Hcov : term_rules_covered excluded l l' = true)
      (Hconserv : forall t t', eq_sort l' [] t t' -> eq_sort l [] t t').

    Lemma term_rule_transfer name c' args t
      : In (name, term_rule c' args t) l' ->
        inb name excluded = false ->
        In (name, term_rule c' args t) l.
    Proof.
      intros Hin Hne.
      unfold term_rules_covered in Hcov.
      rewrite forallb_forall in Hcov.
      specialize (Hcov _ Hin); cbn [snd fst] in Hcov.
      rewrite Hne in Hcov; cbn [orb] in Hcov.
      apply (proj1 (inb_is_In (name, term_rule c' args t) l)).
      rewrite Hcov; exact I.
    Qed.

    Lemma pargs_wf_args (c' : ctx) (s : list term)
      : WfCutElim.P_args V (fun e t => avoids excluded e = true -> Core.wf_term l [] e t) s c' ->
        forallb (avoids excluded) s = true ->
        @Model.wf_args _ _ _ (core_model l) [] s c'.
    Proof.
      revert s; induction c' as [| [n t] c' IH]; intros [|e s]; cbn [WfCutElim.P_args];
        try tauto.
      { intros _ _. constructor. }
      intros [HP HPe] Hf. cbn [forallb] in Hf. apply andb_prop in Hf.
      destruct Hf as [He Hs].
      constructor.
      - apply HPe; exact He.
      - apply IH; assumption.
    Qed.

    Theorem wf_term_transfer : forall (t : sort) (e : term),
        Core.wf_term l' [] e t ->
        avoids excluded e = true ->
        Core.wf_term l [] e t.
    Proof.
      induction 1 using wf_term_cut_ind.
      - rewrite avoids_unfold. intro Hnt.
        apply andb_prop in Hnt. destruct Hnt as [Hname Hargs].
        apply Bool.negb_true_iff in Hname.
        eapply Core.wf_term_by.
        + eapply term_rule_transfer; [ exact H | exact Hname ].
        + apply pargs_wf_args; assumption.
      - destruct H.
      - intro Hnt. eapply Core.wf_term_conv; [ apply IHwf_term; exact Hnt | ].
        apply Hconserv; exact H0.
    Qed.

  End Transfer.

  Theorem wf_term_transfer_check (l l' : lang) (wfl : wf_lang l) (wfl' : wf_lang l')
    (P : V -> bool) (Hstrat : Conservativity.lang_conservative V P l' l = true)
    (excluded : list V) (Hcov : term_rules_covered excluded l l' = true)
    : forall e t, Core.wf_term l' [] e t -> avoids excluded e = true -> Core.wf_term l [] e t.
  Proof.
    intros e t Hwf Havoid.
    eapply wf_term_transfer; eauto.
    intros t1 t2 Heq.
    apply (proj1 (Conservativity.eq_conservative_check V l' l wfl' wfl P
                    Hstrat [] ltac:(constructor) ltac:(constructor))).
    exact Heq.
  Qed.

End WithVar.
