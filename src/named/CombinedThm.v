Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Compilers Elab ElabCompilers ElabCompilersWithPrefix
     SimpleVSubst SimpleVCPS SimpleEvalCtx SimpleEvalCtxCPS SimpleUnit NatHeap SimpleVCPSHeap
     SimpleVFixCPS SimpleVFixCC SimpleVCC SimpleVSTLC SimpleVCCHeap SimpleVFix Matches CompilerTransitivity CompilerTools.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.




(*TODO: put these hints with their subjects*)
Hint Resolve cps_preserving : elab_pfs.
Hint Resolve Ectx_cps_preserving : elab_pfs.
Hint Resolve fix_cps_preserving : elab_pfs.

Hint Resolve ElabCompilers.elab_preserving_compiler_nil : auto_elab.


(*TODO: add let*)
Lemma full_cps_compiler_preserving
  : preserving_compiler
      (heap_cps_ops
         ++ fix_cps_lang
         ++ cps_lang
         ++ cps_prod_lang
         ++ unit_lang
         ++ heap
         ++ nat_exp
         ++ nat_lang
         ++ block_subst
         ++ value_subst)
      (fix_cps++ cps ++ heap_ctx_cps ++ Ectx_cps++ heap_cps++heap_id++cps_subst++[])
      (SimpleVFix.fix_lang++SimpleVSTLC.stlc++ heap_ctx++ eval_ctx++heap_ops++(unit_lang ++ heap ++ nat_exp ++ nat_lang)++(exp_subst ++ value_subst)++[]).
Proof.

  build_compiler.
 
Qed.


Lemma full_cc_compiler_preserving
  : preserving_compiler (fix_cc_lang ++
     heap_cps_ops ++cc_lang ++ forget_eq_wkn ++ unit_eta ++ unit_lang
                                      ++ heap ++ nat_exp ++ nat_lang ++ prod_cc ++
                                      forget_eq_wkn'++
                                      cps_prod_lang ++ block_subst ++ value_subst)
                        (fix_cc++heap_cc++heap_id'++cc++prod_cc_compile++subst_cc++[])
                        (fix_cps_lang++heap_cps_ops++(unit_lang ++ heap ++ nat_exp ++ nat_lang)
                            ++cps_lang++cps_prod_lang++(block_subst ++ value_subst)++[]).
Proof.
  build_compiler.
Qed.



Lemma preserving_compiler_embed tgt cmp src tgt'
    : preserving_compiler tgt cmp src ->
      incl tgt tgt' ->
      preserving_compiler tgt' cmp src.
Proof.
  induction 1; basic_goal_prep; constructor; basic_core_crush.
  eapply wf_sort_lang_monotonicity; eauto.
  eapply wf_term_lang_monotonicity; eauto.
  eapply eq_sort_lang_monotonicity; eauto.
  eapply eq_term_lang_monotonicity; eauto.
Qed.
Hint Resolve preserving_compiler_embed : auto_elab.

Lemma full_compiler_preserving
  : preserving_compiler (fix_cc_lang ++
                                     heap_cps_ops ++cc_lang ++ forget_eq_wkn ++ unit_eta ++ unit_lang
                                     ++ heap ++ nat_exp ++ nat_lang ++ prod_cc ++
                                     forget_eq_wkn'++
                                     cps_prod_lang ++ block_subst ++ value_subst)
                        (compile_cmp (fix_cc++heap_cc++heap_id'++cc++prod_cc_compile++subst_cc++[])
                        (fix_cps++ cps ++ heap_ctx_cps ++ Ectx_cps++ heap_cps++heap_id++cps_subst++[]))
      (SimpleVFix.fix_lang++SimpleVSTLC.stlc++ heap_ctx++ eval_ctx++heap_ops++(unit_lang ++ heap ++ nat_exp ++ nat_lang)++(exp_subst ++ value_subst)++[]).
Proof.
  apply preservation_transitivity
        with (ir:=(fix_cps_lang++heap_cps_ops++(unit_lang ++ heap ++ nat_exp ++ nat_lang)
                               ++cps_lang++cps_prod_lang++(block_subst ++ value_subst)++[])).
  all: try (rewrite <-?app_assoc; solve[prove_from_known_elabs]).
  apply full_cc_compiler_preserving.
  eapply preserving_compiler_embed.
  apply full_cps_compiler_preserving.
  solve_incl.
Qed.

Lemma full_compiler_semantic
  : semantics_preserving
      (fix_cc_lang ++ heap_cps_ops ++cc_lang ++ forget_eq_wkn ++ unit_eta ++ unit_lang
                   ++ heap ++ nat_exp ++ nat_lang ++ prod_cc ++
                   forget_eq_wkn'++
                   cps_prod_lang ++ block_subst ++ value_subst)
      (compile_cmp (fix_cc++heap_cc++heap_id'++cc++prod_cc_compile++subst_cc++[])
                   (fix_cps++ cps ++ heap_ctx_cps ++ Ectx_cps++ heap_cps++heap_id++cps_subst++[]))
      (SimpleVFix.fix_lang++SimpleVSTLC.stlc++ heap_ctx++ eval_ctx++heap_ops++(unit_lang ++ heap ++ nat_exp ++ nat_lang)++(exp_subst ++ value_subst)++[]).
Proof.
  apply inductive_implies_semantic.
  (rewrite <-?app_assoc; solve[prove_from_known_elabs]).
  (rewrite <-?app_assoc; solve[prove_from_known_elabs]).
  apply full_compiler_preserving.
Qed.
  
(*TODO: let expressions too*)
Definition swapfun :=
  {{e #"lambda" #"nat"
      (#"let" (#"get" {ovar 0})
      (#"lambda" #"nat"
        (#"let" (#"get" {ovar 0})
          (#"let" (#"set" {ovar 3} {ovar 0})
            (#"set" {ovar 2} {ovar 3})))))}}.

Definition heap_swap :=
  {{e #"config" (#"hset" (#"hset" "H" "l" "n'") "l'" "m")
      (#"app" (#"app" {swapfun} (#"nv" "l")) (#"nv" "l'"))}}.
