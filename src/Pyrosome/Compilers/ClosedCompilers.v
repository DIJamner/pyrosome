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

  Section WithLangAndCtx.
    Context (l : lang)
      (c : ctx)
      {CM : ClosedModel}
      {CMok : ClosedModel_ok l c}.

    (* --- Prop-valued evaluation of a proof tree into the ClosedModel.
       This is Gluing/Eval.v's [eval] ported from the Type-valued CutTModel to
       the Prop-valued ClosedModel; because [pf] is cut-free it is a direct fold,
       one constructor per ClosedModel_ok operation, with no substitution case. *)
    Local Notation Pp p :=
      ((forall t1 t2, check_sort_proof l c p = Some (t1, t2) -> ceq_sort (ClosedModel:=CM) t1 t2)
       /\ (forall t e1 e2, check_proof l c p = Some (e1, e2, t) -> ceq_term (ClosedModel:=CM) t e1 e2)).

    Lemma eval_args s
      : fold_right (fun p => and (Pp p)) True s ->
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
        + rewrite Heq. eapply (proj2 Pp_p); eauto.
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
        eauto 8 using cterm_var, cterm_cong, cterm_by, cterm_trans, cterm_sym,
                      cterm_conv, csort_cong, csort_by, csort_trans, csort_sym,
                      eval_args with utils.
    Qed.

    Definition eval_sort p t1 t2
      (H : check_sort_proof l c p = Some (t1, t2)) : ceq_sort (ClosedModel:=CM) t1 t2 :=
      proj1 (eval p) t1 t2 H.

    Definition eval_term p t e1 e2
      (H : check_proof l c p = Some (e1, e2, t)) : ceq_term (ClosedModel:=CM) t e1 e2 :=
      proj2 (eval p) t e1 e2 H.

    Section Soundness.
      Context (wfl : wf_lang l)
        (wfc : wf_ctx (Model := core_model l) c).

      (* A [ClosedModel_ok] is complete for the judgemental equalities: reuse
         tree-proof completeness (CutModelSound) then evaluate the tree. *)
      Theorem closed_model_sound_term t e1 e2
        : eq_term l c t e1 e2 -> ceq_term (ClosedModel:=CM) t e1 e2.
      Proof.
        intro H.
        destruct (CutModelSound.tree_complete_term wfl wfc H) as [p Hp].
        eapply eval_term; eauto.
      Qed.

      Theorem closed_model_sound_sort t1 t2
        : eq_sort l c t1 t2 -> ceq_sort (ClosedModel:=CM) t1 t2.
      Proof.
        intro H.
        destruct (proj1 (CutModelSound.tree_complete wfl wfc) _ _ H) as [p Hp].
        eapply eval_sort; eauto.
      Qed.

    End Soundness.

  End WithLangAndCtx.

  (* --- From the per-rule inductive [preserving_closed_compiler_ext] to the
     semantic [preserving_closed_compiler] (i.e. the pullback is a
     [ClosedModel_ok]).  The four "lookup" lemmas turn the derivation into the
     obligation for a named rule; the theorem then assembles the record,
     discharging the variable case and the structural (trans/sym/conv) laws
     directly from the *target* model's [ClosedModel_ok] -- so those are never
     obligations for the compiler author. *)
  Section ExtSoundness.
    Context (cmp : closed_compiler V) (CM : @ClosedModel V).

    Lemma pcce_term_rule_lookup
      : forall l, preserving_closed_compiler_ext cmp CM l ->
        forall n c' args t, In (n, term_rule c' args t) l ->
        forall s1 s2, ceq_args (CM := compile_model cmp CM) c' s1 s2 ->
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
        forall s1 s2, ceq_args (CM := compile_model cmp CM) c' s1 s2 ->
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
        forall s1 s2, ceq_args (CM := compile_model cmp CM) c' s1 s2 ->
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
        forall s1 s2, ceq_args (CM := compile_model cmp CM) c' s1 s2 ->
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

    (* The ext inductive yields the pullback [ClosedModel_ok].  The target
       [ClosedModel_ok] is needed only at ambient context [compile_ctx cmp c] and
       only for its variable rule and its equational structural laws. *)
    Theorem preserving_closed_compiler_ext_sound
      (l : lang) (c : ctx) (l_tgt : lang)
      (CMok : ClosedModel_ok l_tgt (compile_ctx cmp c))
      (Hext : preserving_closed_compiler_ext cmp CM l)
      : preserving_closed_compiler cmp l c CM.
    Proof.
      unfold preserving_closed_compiler.
      unshelve econstructor; cbn [compile_model ceq_sort ceq_term].
      - (* cterm_var *)
        intros n t Hin.
        change (compile cmp (var n)) with (var n).
        apply CMok.(cterm_var).
        apply in_named_map; exact Hin.
      - (* cterm_cong *)
        intros c' name args t s1 s2 Hin Hargs.
        eapply pcce_term_rule_lookup; eauto.
      - (* cterm_by *)
        intros c' name e1 e2 t s1 s2 Hin Hargs.
        eapply pcce_term_eq_lookup; eauto.
      - (* cterm_trans *)
        intros t e1 e12 e2 H1 H2; eapply CMok.(cterm_trans); eauto.
      - (* cterm_sym *)
        intros t e1 e2 H1; eapply CMok.(cterm_sym); eauto.
      - (* cterm_conv *)
        intros t1 t2 e1 e2 H1 H2; eapply CMok.(cterm_conv); eauto.
      - (* csort_cong *)
        intros c' name args s1 s2 Hin Hargs.
        eapply pcce_sort_rule_lookup; eauto.
      - (* csort_by *)
        intros c' name t1 t2 s1 s2 Hin Hargs.
        eapply pcce_sort_eq_lookup; eauto.
      - (* csort_trans *)
        intros t1 t12 t2 H1 H2; eapply CMok.(csort_trans); eauto.
      - (* csort_sym *)
        intros t1 t2 H1; eapply CMok.(csort_sym); eauto.
    Qed.

  End ExtSoundness.

  (* --- Main theorem: a preserving closed compiler preserves the judgemental
     equalities.  Because preservation is *defined* as the pullback being a
     ClosedModel_ok, each conclusion is a one-line instance of soundness above:
     no substitution lemmas, no target Model_ok, no strengthening. *)
  Section Preservation.
    Context (l : lang)
      (wfl : wf_lang l)
      (c : ctx)
      (wfc : wf_ctx (Model := core_model l) c)
      (cmp : closed_compiler V)
      (CM : ClosedModel)
      (Hpres : preserving_closed_compiler cmp l c CM).

    Theorem closed_sort_eq_preserving t1 t2
      : eq_sort l c t1 t2 ->
        ceq_sort (ClosedModel:=CM) (compile_sort cmp t1) (compile_sort cmp t2).
    Proof.
      exact (@closed_model_sound_sort l c (compile_model cmp CM) Hpres wfl wfc t1 t2).
    Qed.

    Theorem closed_term_eq_preserving t e1 e2
      : eq_term l c t e1 e2 ->
        ceq_term (ClosedModel:=CM) (compile_sort cmp t) (compile cmp e1) (compile cmp e2).
    Proof.
      exact (@closed_model_sound_term l c (compile_model cmp CM) Hpres wfl wfc t e1 e2).
    Qed.

  End Preservation.

  (* --- The compiler-author-facing entry point: from the per-rule inductive
     [preserving_closed_compiler_ext] (one obligation per source rule) directly
     to semantics preservation, given a well-formed target model at the compiled
     ambient context.  No pullback record is ever exposed to the author. *)
  Section PreservationFromExt.
    Context (l : lang)
      (wfl : wf_lang l)
      (c : ctx)
      (wfc : wf_ctx (Model := core_model l) c)
      (l_tgt : lang)
      (cmp : closed_compiler V)
      (CM : ClosedModel)
      (CMok : ClosedModel_ok l_tgt (compile_ctx cmp c))
      (Hext : preserving_closed_compiler_ext cmp CM l).

    Lemma preserving_from_ext : preserving_closed_compiler cmp l c CM.
    Proof. eapply preserving_closed_compiler_ext_sound; eauto. Qed.

    Theorem closed_sort_eq_preserving_ext t1 t2
      : eq_sort l c t1 t2 ->
        ceq_sort (ClosedModel:=CM) (compile_sort cmp t1) (compile_sort cmp t2).
    Proof.
      exact (@closed_model_sound_sort l c (compile_model cmp CM) preserving_from_ext
               wfl wfc t1 t2).
    Qed.

    Theorem closed_term_eq_preserving_ext t e1 e2
      : eq_term l c t e1 e2 ->
        ceq_term (ClosedModel:=CM) (compile_sort cmp t) (compile cmp e1) (compile cmp e2).
    Proof.
      exact (@closed_model_sound_term l c (compile_model cmp CM) preserving_from_ext
               wfl wfc t e1 e2).
    Qed.

  End PreservationFromExt.

End WithVar.
