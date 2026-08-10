Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Monad.
From Pyrosome.Theory Require Import Core ClosedModel.
From Pyrosome.Proof Require Import TreeProofs.
From Pyrosome.Gluing Require CutModelSound.
From Pyrosome.Compilers Require Import ClosedCompilerDefs.
Import Core.Notations.

(* Keep eqb folded so the checker's [eqb x x] guards stay visible to eqb_refl. *)
Local Arguments eqb : simpl never.

Section WithVar.
  Context (V : Type)
    {V_Eqb : Eqb V}
    {V_Eqb_ok : Eqb_ok V_Eqb}
    {V_default : WithDefault V}.

  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation lang := (@lang V).

  Section WithTarget.
    Context {tgt_term tgt_sort : Type}
      {tgt_term_default : WithDefault tgt_term}
      {tgt_sort_default : WithDefault tgt_sort}.

    (* --- From the per-rule inductive [preserving_closed_compiler_ext] to the
       per-rule obligation for a named rule, phrased in the target model [CM] on
       the compiled syntax.  These four "lookup" lemmas are the source of the
       congruence / axiom-instance facts that [eval] folds into the model. *)
    Section ExtLookups.
      Context (cmp : closed_compiler V tgt_term tgt_sort)
        (CM : ClosedModel tgt_term tgt_sort).

      Lemma pcce_term_rule_lookup
        : forall l, preserving_closed_compiler_ext cmp CM l ->
          forall n c' args t, In (n, term_rule c' args t) l ->
          forall s1 s2, ceq_args (compile_model cmp CM) c' s1 s2 ->
            ceq_term (ClosedModel := CM) (compile_sort cmp (t [/with_names_from c' s2/]))
              (compile cmp (con n s1)) (compile cmp (con n s2)).
      Proof.
        intros l H.
        induction H as
          [ | l n c' args Hpre IH Hob
            | l n c' args t Hpre IH Hob
            | l n c' t1 t2 Hpre IH Hob
            | l n c' e1 e2 t Hpre IH Hob ];
          intros nn cc aa tt Hin s1 s2 Hargs.
        - destruct Hin.
        - destruct Hin as [Heq | Hin]; [ inversion Heq | ]; eapply IH; eauto.
        - destruct Hin as [Heq | Hin];
            [ inversion Heq; subst; eapply Hob; eauto | eapply IH; eauto ].
        - destruct Hin as [Heq | Hin]; [ inversion Heq | ]; eapply IH; eauto.
        - destruct Hin as [Heq | Hin]; [ inversion Heq | ]; eapply IH; eauto.
      Qed.

      Lemma pcce_sort_rule_lookup
        : forall l, preserving_closed_compiler_ext cmp CM l ->
          forall n c' args, In (n, sort_rule c' args) l ->
          forall s1 s2, ceq_args (compile_model cmp CM) c' s1 s2 ->
            ceq_sort (ClosedModel := CM)
              (compile_sort cmp (scon n s1)) (compile_sort cmp (scon n s2)).
      Proof.
        intros l H.
        induction H as
          [ | l n c' args Hpre IH Hob
            | l n c' args t Hpre IH Hob
            | l n c' t1 t2 Hpre IH Hob
            | l n c' e1 e2 t Hpre IH Hob ];
          intros nn cc aa Hin s1 s2 Hargs.
        - destruct Hin.
        - destruct Hin as [Heq | Hin];
            [ inversion Heq; subst; eapply Hob; eauto | eapply IH; eauto ].
        - destruct Hin as [Heq | Hin]; [ inversion Heq | ]; eapply IH; eauto.
        - destruct Hin as [Heq | Hin]; [ inversion Heq | ]; eapply IH; eauto.
        - destruct Hin as [Heq | Hin]; [ inversion Heq | ]; eapply IH; eauto.
      Qed.

      Lemma pcce_sort_eq_lookup
        : forall l, preserving_closed_compiler_ext cmp CM l ->
          forall n c' t1 t2, In (n, sort_eq_rule c' t1 t2) l ->
          forall s1 s2, ceq_args (compile_model cmp CM) c' s1 s2 ->
            ceq_sort (ClosedModel := CM)
              (compile_sort cmp (t1 [/with_names_from c' s1/]))
              (compile_sort cmp (t2 [/with_names_from c' s2/])).
      Proof.
        intros l H.
        induction H as
          [ | l n c' args Hpre IH Hob
            | l n c' args t Hpre IH Hob
            | l n c' t1 t2 Hpre IH Hob
            | l n c' e1 e2 t Hpre IH Hob ];
          intros nn cc tt1 tt2 Hin s1 s2 Hargs.
        - destruct Hin.
        - destruct Hin as [Heq | Hin]; [ inversion Heq | ]; eapply IH; eauto.
        - destruct Hin as [Heq | Hin]; [ inversion Heq | ]; eapply IH; eauto.
        - destruct Hin as [Heq | Hin];
            [ inversion Heq; subst; eapply Hob; eauto | eapply IH; eauto ].
        - destruct Hin as [Heq | Hin]; [ inversion Heq | ]; eapply IH; eauto.
      Qed.

      Lemma pcce_term_eq_lookup
        : forall l, preserving_closed_compiler_ext cmp CM l ->
          forall n c' e1 e2 t, In (n, term_eq_rule c' e1 e2 t) l ->
          forall s1 s2, ceq_args (compile_model cmp CM) c' s1 s2 ->
            ceq_term (ClosedModel := CM) (compile_sort cmp (t [/with_names_from c' s2/]))
              (compile cmp (e1 [/with_names_from c' s1/]))
              (compile cmp (e2 [/with_names_from c' s2/])).
      Proof.
        intros l H.
        induction H as
          [ | l n c' args Hpre IH Hob
            | l n c' args t Hpre IH Hob
            | l n c' t1 t2 Hpre IH Hob
            | l n c' ee1 ee2 t Hpre IH Hob ];
          intros nn cc ff1 ff2 tt Hin s1 s2 Hargs.
        - destruct Hin.
        - destruct Hin as [Heq | Hin]; [ inversion Heq | ]; eapply IH; eauto.
        - destruct Hin as [Heq | Hin]; [ inversion Heq | ]; eapply IH; eauto.
        - destruct Hin as [Heq | Hin]; [ inversion Heq | ]; eapply IH; eauto.
        - destruct Hin as [Heq | Hin];
            [ inversion Heq; subst; eapply Hob; eauto | eapply IH; eauto ].
      Qed.

    End ExtLookups.

    Section Eval.
      Context (l : lang)
        (cmp : closed_compiler V tgt_term tgt_sort)
        (CM : ClosedModel tgt_term tgt_sort)
        (CMok : ClosedModel_ok CM)
        (Hext : preserving_closed_compiler_ext cmp CM l).

      (* The pullback of the target [CM] along [compile]; a [ClosedModel] over the
         source syntax whose judgments are exactly the preservation conclusions.
         Its judgments unfold to [CM]'s at the compiled syntax, so the fold below
         discharges them with [CM]'s own structural laws ([CMok]) and the per-rule
         congruence/axiom facts ([pcce_*_lookup], from [Hext]) directly. *)
      Local Notation M := (compile_model cmp CM).

      (* The target model's structural laws, as plain references (so they can be
         named in [eauto ... using] below). *)
      Let ct_trans := CMok.(cterm_trans).
      Let ct_sym := CMok.(cterm_sym).
      Let ct_conv := CMok.(cterm_conv).
      Let cs_trans := CMok.(csort_trans).
      Let cs_sym := CMok.(csort_sym).

      (* --- Prop-valued evaluation of a proof tree into the pullback model [M].
         This is Gluing/Eval.v's [eval] ported to the Prop-valued, closed
         setting: the ambient context is empty (so the [pvar] case is vacuous). *)
      Local Notation Pp p :=
        ((forall t1 t2, check_sort_proof l [] p = Some (t1, t2) -> ceq_sort (ClosedModel:=M) t1 t2)
         /\ (forall t e1 e2, check_proof l [] p = Some (e1, e2, t) -> ceq_term (ClosedModel:=M) t e1 e2)).

      Lemma eval_args s
        : fold_right (fun p => and (Pp p)) True s ->
          forall c' lhs rhs,
            check_args_proof (check_proof l []) s c' = Some (lhs, rhs) ->
            ceq_args M c' lhs rhs.
      Proof.
        induction s as [| p s IHs]; intros IH c' lhs rhs Hc.
        - destruct c'; cbn in Hc; try discriminate.
          safe_invert Hc. constructor.
        - destruct IH as [Pp_p IH_s].
          destruct c' as [| [name t] c'']; cbn in Hc; try discriminate.
          destruct (check_args_proof (check_proof l []) s c'') as [[lhs0 rhs0] |] eqn:Hargs;
            cbn in Hc; try discriminate.
          destruct (check_proof l [] p) as [[[e1 e2] t'] |] eqn:Hp;
            cbn in Hc; try discriminate.
          destruct (eqb t[/with_names_from c'' rhs0/] t') eqn:Heqb;
            cbn in Hc; try discriminate.
          safe_invert Hc.
          assert (t[/with_names_from c'' rhs0/] = t') as Heq.
          { apply (proj1 (eqb_prop_iff _ _ _)); rewrite Heqb; exact I. }
          econstructor.
          + eapply IHs; eauto.
          + assert (Hct : ceq_term (ClosedModel:=M) t' e1 e2)
              by (eapply (proj2 Pp_p); reflexivity).
            rewrite <- Heq in Hct.
            exact Hct.
      Qed.

      Theorem eval p : Pp p.
      Proof.
        induction p; split; intros; cbn in *;
          repeat (lazymatch goal with
                  | [ HH : context [ match ?x with _ => _ end ] |- _ ] =>
                      destruct x eqn:?
                  end; try discriminate);
          try discriminate;
          repeat (lazymatch goal with
                  | [ HH : Some _ = Some _ |- _ ] => safe_invert HH
                  | [ HH : _ /\ _ |- _ ] => destruct HH
                  | [ HH : named_list_lookup_err _ _ = Some _ |- _ ] => symmetry in HH
                  | [ HH : eqb ?a ?b = true |- _ ] =>
                      let Heq := fresh "Heq" in
                      assert (a = b) as Heq
                        by (apply (proj1 (eqb_prop_iff _ _ _)); rewrite HH; exact I);
                      clear HH; try subst a; try subst b
                  end);
          eauto 8 using pcce_term_rule_lookup, pcce_term_eq_lookup,
                        pcce_sort_rule_lookup, pcce_sort_eq_lookup,
                        ct_trans, ct_sym, ct_conv, cs_trans, cs_sym,
                        eval_args with utils.
      Qed.

      Definition eval_sort p t1 t2
        (H : check_sort_proof l [] p = Some (t1, t2)) : ceq_sort (ClosedModel:=M) t1 t2 :=
        proj1 (eval p) t1 t2 H.

      Definition eval_term p t e1 e2
        (H : check_proof l [] p = Some (e1, e2, t)) : ceq_term (ClosedModel:=M) t e1 e2 :=
        proj2 (eval p) t e1 e2 H.

      Section Soundness.
        Context (wfl : wf_lang l).

        (* The pullback is complete for the judgemental equalities of closed
           terms: reuse tree-proof completeness (CutModelSound) then evaluate the
           tree.  The ambient context is empty, so [wf_ctx] is trivial. *)
        Theorem closed_model_sound_term t e1 e2
          : eq_term l [] t e1 e2 -> ceq_term (ClosedModel:=M) t e1 e2.
        Proof.
          intro H.
          assert (wfc : wf_ctx (Model := core_model l) []) by constructor.
          destruct (CutModelSound.tree_complete_term wfl wfc H) as [p Hp].
          eapply eval_term; eauto.
        Qed.

        Theorem closed_model_sound_sort t1 t2
          : eq_sort l [] t1 t2 -> ceq_sort (ClosedModel:=M) t1 t2.
        Proof.
          intro H.
          assert (wfc : wf_ctx (Model := core_model l) []) by constructor.
          destruct (proj1 (CutModelSound.tree_complete wfl wfc) _ _ H) as [p Hp].
          eapply eval_sort; eauto.
        Qed.

      End Soundness.

    End Eval.

    (* --- Main theorem: a preserving closed compiler preserves the judgemental
       equalities of closed terms/sorts.  Directly from the per-rule inductive
       [preserving_closed_compiler_ext] and the target model's structural laws;
       no substitution lemmas and no pullback record are exposed to the author. *)
    Section Preservation.
      Context (l : lang)
        (wfl : wf_lang l)
        (cmp : closed_compiler V tgt_term tgt_sort)
        (CM : ClosedModel tgt_term tgt_sort)
        (CMok : ClosedModel_ok CM)
        (Hext : preserving_closed_compiler_ext cmp CM l).

      Theorem closed_sort_eq_preserving t1 t2
        : eq_sort l [] t1 t2 ->
          ceq_sort (ClosedModel:=CM) (compile_sort cmp t1) (compile_sort cmp t2).
      Proof.
        exact (@closed_model_sound_sort l cmp CM CMok Hext wfl t1 t2).
      Qed.

      Theorem closed_term_eq_preserving t e1 e2
        : eq_term l [] t e1 e2 ->
          ceq_term (ClosedModel:=CM) (compile_sort cmp t) (compile cmp e1) (compile cmp e2).
      Proof.
        exact (@closed_model_sound_term l cmp CM CMok Hext wfl t e1 e2).
      Qed.

    End Preservation.

  End WithTarget.

End WithVar.
