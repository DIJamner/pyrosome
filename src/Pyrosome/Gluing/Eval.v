Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Monad.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Proof Require Import TreeProofs.
From Pyrosome.Gluing Require Import CutTModel.
Import Core.Notations.

(* The generic evaluation: TreeProofs.pf_checker_sound generalized to an arbitrary
   cut-free target.  Because pf is cut-free, this is a direct fold over the proof
   term — each constructor maps to the matching CutTModel_ok operation, with no
   substitution case to handle. *)
Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
          {V_Eqb_ok : Eqb_ok V_Eqb}
          {V_default : WithDefault V}.

  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation lang := (@lang V).
  Notation pf := (@pf V).

  Section Eval.
    Context (l : lang)
            (c : ctx)
            {CM : CutTModel}
            {CMok : CutTModel_ok l c}.

    (* combined per-proof-term property (sort- and term-equality).  The ambient
       context [c] is fixed (it never changes during the cut-free fold). *)
    Local Notation Pp p :=
      (((forall t1 t2, check_sort_proof l c p = Some (t1, t2) -> ceq_sort (CutTModel:=CM) t1 t2)
        * (forall t e1 e2, check_proof l c p = Some (e1, e2, t) -> ceq_term (CutTModel:=CM) t e1 e2))%type).

    (* The argument-list fold, consuming the positional (fold_right prod) IH that
       pf_rect produces for the [pcon] case. *)
    Lemma eval_args s
      : fold_right (fun p => prod (Pp p)) unit s ->
        forall c' lhs rhs,
          check_args_proof (check_proof l c) s c' = Some (lhs, rhs) ->
          ceq_args (CM:=CM) c' lhs rhs.
    Proof.
      induction s as [| p s IHs]; intros IH c' lhs rhs Hc.
      - destruct c'; cbn in Hc; try discriminate.
        safe_invert Hc. constructor.
      - destruct IH as [Pp_p IH_s].
        destruct c' as [| [name t] c'']; cbn in Hc; try discriminate.
        destruct (check_args_proof (check_proof l c) s c'') as [[lhs0 rhs0] |] eqn:Hargs;
          cbn in Hc; try discriminate.
        destruct (check_proof l c p) as [[[e1 e2] t'] |] eqn:Hp;
          cbn in Hc; try discriminate.
        destruct (eqb t[/with_names_from c'' rhs0/] t') eqn:Heqb;
          cbn in Hc; try discriminate.
        safe_invert Hc.
        assert (t[/with_names_from c'' rhs0/] = t') as Heq.
        { apply (proj1 (eqb_prop_iff _ _ _)); rewrite Heqb; exact I. }
        econstructor.
        + eapply IHs; eauto.
        + rewrite Heq. eapply (snd Pp_p); eauto.
    Qed.

    Theorem eval p : Pp p.
    Proof.
      induction p; split; intros; cbn in *;
        (* break down all the matches in the check-equation H *)
        repeat (lazymatch goal with
                | [ HH : context [ match ?x with _ => _ end ] |- _ ] =>
                    destruct x eqn:?
                end; try discriminate);
        (* close the None = Some cases with no remaining match (pvar/pconv sort) *)
        try discriminate;
        (* clean up: invert Some=Some, split IH pairs, orient lookups,
           convert eqb-true into propositional eq and substitute *)
        repeat (lazymatch goal with
                | [ HH : Some _ = Some _ |- _ ] => safe_invert HH
                | [ HH : _ * _ |- _ ] => destruct HH
                | [ HH : named_list_lookup_err _ _ = Some _ |- _ ] => symmetry in HH
                | [ HH : eqb ?a ?b = true |- _ ] =>
                    let Heq := fresh "Heq" in
                    assert (a = b) as Heq
                      by (apply (proj1 (eqb_prop_iff _ _ _)); rewrite HH; exact I);
                    clear HH; try subst a; try subst b
                end);
        (* every remaining case maps to one cut-free operation *)
        eauto 8 using cterm_var, cterm_cong, cterm_by, cterm_trans, cterm_sym,
                      cterm_conv, csort_cong, csort_by, csort_trans, csort_sym,
                      eval_args with utils.
    Qed.

    Definition eval_sort p t1 t2
      (H : check_sort_proof l c p = Some (t1, t2)) : ceq_sort (CutTModel:=CM) t1 t2 :=
      fst (eval p) t1 t2 H.

    Definition eval_term p t e1 e2
      (H : check_proof l c p = Some (e1, e2, t)) : ceq_term (CutTModel:=CM) t e1 e2 :=
      snd (eval p) t e1 e2 H.

  End Eval.

End WithVar.
