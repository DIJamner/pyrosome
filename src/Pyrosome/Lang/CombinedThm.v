Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils GallinaHintDb.
From Pyrosome Require Import Theory.Core Compilers.SemanticsPreservingDef
  Compilers.Compilers Compilers.CompilerFacts
  Elab.Elab Elab.ElabCompilers
  Tools.CompilerTools Compilers.CompilerTransitivity
  Tools.Matches Tools.EGraph.Automation
  Tools.EGraph.TypeInference
  Tools.EGraph.ComputeWf
  Tools.Resolution.
From Pyrosome.Lang Require Import
  PolySubst SimpleVSubst SimpleVCPS SimpleEvalCtx SimpleEvalCtxCPS
  SimpleUnit NatHeap SimpleVCPS SimpleVCPSHeap Let
  SimpleVFixCPS SimpleVFixCC SimpleVCC SimpleVSTLC SimpleVCCHeap SimpleVFix.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.

Local Notation compiler_case := (compiler_case string (tgt_term:=term) (tgt_sort:=sort)).

(*TODO: move to compilerdefs.v*)
#[export] Instance compiler_case_Eqb : Eqb compiler_case :=
  fun c1 c2 =>
    match c1, c2 with
    | sort_case args t, sort_case args' t' =>
        (eqb args args') && (eqb t t')
    | term_case args t, term_case args' t' =>
        (eqb args args') && (eqb t t')
    | _,_ => false
    end%bool.

#[export] Instance compiler_case_Eqb_ok : Eqb_ok compiler_case_Eqb.
Proof.
  intros a b;
    destruct a, b;
    cbn [eqb compiler_case_Eqb];
    try congruence.
  all: case_match;
    basic_core_crush.
Qed.

#[local] Hint Resolve ElabCompilers.elab_preserving_compiler_nil : auto_elab.

#[local] Hint Resolve incl_nil_l : utils.

Lemma wf_lang_concat {V} `{Eqb_ok V} `{WithDefault V} (l : Rule.lang V) l1 l2
  : wf_lang_ext l l1 ->
    wf_lang_ext (l1 ++ l) l2 ->
    wf_lang_ext l (l2 ++ l1).
Proof.
  induction 2; basic_goal_prep; basic_core_firstorder_crush.
  rewrite <- app_assoc; auto.
Qed.
#[local] Hint Resolve wf_lang_concat : lang_core.


Definition src_ext := (SimpleVFix.fix_lang++SimpleVSTLC.stlc++ heap_ctx++ eval_ctx++heap_ops++(unit_lang ++ heap ++ nat_exp ++ nat_lang)).

Definition ir_ext :=
  fix_cps_lang++heap_cps_ops++(unit_lang ++ heap ++ nat_exp ++ nat_lang)
                            ++cps_lang++cps_prod_lang.

Definition tgt_ext :=
  fix_cc_lang ++ heap_cps_ops ++cc_lang ++ forget_eq_wkn ++ unit_eta ++ unit_lang
                   ++ heap ++ nat_exp ++ nat_lang ++ prod_cc ++
                   forget_eq_wkn'++
                   cps_prod_lang.

Lemma full_cps_compiler_preserving
  : preserving_compiler_ext
      (tgt_Model := core_model (ir_ext ++ block_subst ++ value_subst))
      []
      (let_cps ++fix_cps++ cps ++ heap_ctx_cps ++ Ectx_cps++ heap_cps++heap_id++cps_subst++[])
      (let_lang++ src_ext++exp_subst ++ value_subst).
Proof. prove_by_cmp_db. Qed.

Lemma full_cc_compiler_preserving
  : preserving_compiler_ext
      (tgt_Model := core_model (tgt_ext ++ block_subst ++ value_subst))
      []
      (fix_cc++heap_cc++heap_id'++cc++prod_cc_compile++subst_cc++[])
      (ir_ext++block_subst ++ value_subst).
Proof. prove_by_cmp_db. Qed.

Lemma full_compiler_preserving
  : preserving_compiler_ext
      (tgt_Model := core_model (tgt_ext ++ block_subst ++ value_subst))
      []
      (compile_cmp (fix_cc++heap_cc++heap_id'++cc++prod_cc_compile++subst_cc++[])
         (let_cps++fix_cps++ cps ++ heap_ctx_cps
            ++ Ectx_cps++ heap_cps++heap_id++cps_subst++[]))
      (let_lang ++ src_ext++exp_subst ++ value_subst).
Proof.
  apply preservation_transitivity
        with (ir:=ir_ext ++ block_subst ++ value_subst).
  all: try (rewrite <-?app_assoc; solve[unfold src_ext, ir_ext, tgt_ext;prove_by_lang_db]).
  all: try typeclasses eauto; try reflexivity.
  {
    apply full_cc_compiler_preserving.
  }
  {
    eapply preserving_compiler_embed.
    1: apply full_cps_compiler_preserving.
    compute_incl.
  }
Qed.

Notation semantics_preserving tgt cmp :=
  (semantics_preserving (tgt_Model := core_model tgt)
     (compile cmp)
     (compile_sort cmp)
     (compile_ctx cmp)
     (compile_args cmp)
     (compile_subst cmp)).

Lemma full_compiler_semantic
  : semantics_preserving
      (tgt_ext ++ block_subst ++ value_subst)
      (compile_cmp (fix_cc++heap_cc++heap_id'++cc++prod_cc_compile++subst_cc++[])
         (let_cps++fix_cps++ cps ++ heap_ctx_cps
            ++ Ectx_cps++ heap_cps++heap_id++cps_subst++[]))
      (let_lang++src_ext ++ exp_subst ++ value_subst).
Proof.
  apply inductive_implies_semantic; try typeclasses eauto;
    eauto using ModelImpls.core_model_ok; try reflexivity.
  1: apply ModelImpls.core_model_ok; try typeclasses eauto.
  1: solve [unfold src_ext, ir_ext, tgt_ext; prove_by_lang_db].
  1: solve [unfold src_ext, ir_ext, tgt_ext; prove_by_lang_db].
  apply full_compiler_preserving.
Qed.

Definition full_compiler :=
  (compile_cmp (fix_cc++heap_cc++heap_id'++cc++prod_cc_compile++subst_cc++[])
     (let_cps++fix_cps++ cps ++ heap_ctx_cps ++ Ectx_cps++ heap_cps++heap_id++cps_subst++[])).

Require Import Pyrosome.Compilers.PartialEval.

Definition compile_fn l c t e :=
  partial_eval _ l (compile_ctx full_compiler c) (compile_sort full_compiler t) 100 (compile full_compiler e).

Lemma full_compiler_with_opt_pres_eq
  (src := let_lang++src_ext ++ exp_subst ++ value_subst)
  (tgt := tgt_ext  ++ block_subst ++ value_subst)
  : forall c t e1 e2,
      eq_term src c t e1 e2 ->
      wf_ctx (Model:=core_model src) c ->
      eq_term tgt (compile_ctx full_compiler c) (compile_sort full_compiler t)
        (compile_fn tgt c t e1) (compile_fn tgt c t e2).
Proof.
  intros.
  unfold compile_fn.
  unshelve (eapply eq_term_trans; [eapply eq_term_trans; [eapply eq_term_sym|shelve]|];
            eapply partial_eval_correct;
            try eapply full_compiler_semantic;
            eauto; try typeclasses eauto).
  {
    eapply full_compiler_semantic; eauto.
  }
  1,3:[>prove_by_lang_db ..].
  {
    eapply eq_term_wf_l; eauto; try typeclasses eauto.
    prove_by_lang_db.
  }
  {
    eapply eq_term_wf_r; eauto; try typeclasses eauto.
    prove_by_lang_db.
  }
Qed.
