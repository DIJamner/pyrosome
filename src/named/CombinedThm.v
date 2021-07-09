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



(*TODO: put in right place*)

Import SumboolNotations.

Definition case_eq_dec (r1 r2 : compiler_case) : {r1 = r2} + {~ r1 = r2}.
  refine(match r1, r2 with
         | sort_case args t, sort_case args' t' =>
           SB! (list_eq_dec string_dec args args') SB&
           (sort_eq_dec t t')
         | term_case args t, term_case args' t' =>
           SB! (list_eq_dec string_dec args args') SB&
           (term_eq_dec t t')
         | _,_ => _
         end); autorewrite with utils lang_core; try intuition fail.
  all: right.
  all: intros; basic_core_crush.
Defined.

Definition compute_incl_compiler (l1 l2 : compiler) :=
  if incl_dec (pair_eq_dec string_dec case_eq_dec) l1 l2 then true else false.

Lemma use_compute_incl_compiler l1 l2
  : compute_incl_compiler l1 l2 = true -> incl l1 l2.
Proof.
  unfold compute_incl_compiler.
  destruct (incl_dec _ l1 l2); easy.
Qed.

Ltac solve_incl := 
  solve [auto with utils
        | apply use_compute_incl_compiler; vm_compute; reflexivity
        | apply use_compute_incl_lang; vm_compute; reflexivity].

Ltac use_preserving_hint :=
  eapply elab_preserving_compiler_embed;
  [eapply elab_preserving_compiler_monotonicity;[shelve| | shelve |..];
   [ eauto with elab_pfs| solve_incl|apply use_compute_all_fresh; vm_compute; reflexivity]
  | solve_incl].

(*TODO: put these hints with their subjects*)
Hint Resolve cps_preserving : elab_pfs.
Hint Resolve Ectx_cps_preserving : elab_pfs.
Hint Resolve fix_cps_preserving : elab_pfs.

Hint Resolve ElabCompilers.elab_preserving_compiler_nil : auto_elab.


(*
TODO: these proofs should be fully automated
 *)


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
  eapply elab_compiler_implies_preserving.
  repeat eapply elab_compiler_prefix_implies_elab; eauto with elab_pfs auto_elab.
  {
    eapply elab_preserving_compiler_embed.
    eapply cps_subst_preserving.
    solve_incl.
  }
  {
    eapply elab_preserving_compiler_embed.
    eapply cps_preserving.
    solve_incl.
  }
  {
    eapply elab_preserving_compiler_embed.
    eapply heap_cps_preserving.
    solve_incl.
  }
  {
    eapply elab_preserving_compiler_embed.
    eapply elab_preserving_compiler_monotonicity.
    2:eapply Ectx_cps_preserving.
    change (cps_subst) with (cps_subst++[]).
    eapply elab_compiler_prefix_implies_elab.
    constructor.
    eapply cps_subst_preserving.
    rewrite <-?app_assoc; solve[prove_from_known_elabs].
    solve_incl.
    apply use_compute_all_fresh; vm_compute; reflexivity.
    solve_incl.
  }
  {
    eapply elab_preserving_compiler_embed.
    eapply heap_ctx_cps_preserving.
    solve_incl.
  }
  {
    eapply elab_preserving_compiler_embed.
    eapply elab_preserving_compiler_monotonicity.
    2: eapply SimpleVCPS.cps_preserving.
    change (cps_subst) with (cps_subst++[]).
    eapply elab_compiler_prefix_implies_elab.
    constructor.
    eapply elab_preserving_compiler_embed.
    eapply cps_subst_preserving.
    solve_incl.
    rewrite <-?app_assoc; solve[prove_from_known_elabs].
    solve_incl.
    apply use_compute_all_fresh; vm_compute; reflexivity.
    solve_incl.
  }
  {
    eapply elab_preserving_compiler_embed.
    eapply elab_preserving_compiler_monotonicity.
    2: eapply fix_cps_preserving.
    {
      eapply elab_compiler_prefix_implies_elab.
      {
        change (cps_subst) with (cps_subst++[]).
        eapply elab_compiler_prefix_implies_elab.
        constructor.
        eapply elab_preserving_compiler_embed.
        eapply cps_subst_preserving.
        solve_incl.
      }
      {
        eapply elab_preserving_compiler_embed.
        apply SimpleVCPS.cps_preserving.
        solve_incl.
      }
    }
    rewrite <-?app_assoc; solve[prove_from_known_elabs].
    solve_incl.
    apply use_compute_all_fresh; vm_compute; reflexivity.
    solve_incl.
  }
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
  eapply elab_compiler_implies_preserving.
  repeat eapply elab_compiler_prefix_implies_elab; eauto with elab_pfs auto_elab.
  {
    eapply elab_preserving_compiler_embed.
    eapply subst_cc_preserving.
    solve_incl.
  }
  {
    eapply elab_preserving_compiler_embed.
    eapply prod_cc_preserving.
    solve_incl.
  }
  {
    eapply elab_preserving_compiler_embed.
    eapply cc_preserving.
    solve_incl.
  }
  {
    eapply elab_preserving_compiler_monotonicity.
    2:eapply elab_preserving_compiler_embed.
    2:eapply heap_id'_preserving.
    change (subst_cc) with (subst_cc++[]).
    eapply elab_compiler_prefix_implies_elab.
    constructor.
    eapply elab_preserving_compiler_embed.
    eapply subst_cc_preserving.
    rewrite <-?app_assoc; solve[prove_from_known_elabs].
    solve_incl.
    rewrite <-?app_assoc; solve[prove_from_known_elabs].
    solve_incl.
    apply use_compute_all_fresh; vm_compute; reflexivity.
  }
  {
    eapply elab_preserving_compiler_monotonicity.
    2:eapply elab_preserving_compiler_embed.
    2:eapply heap_cc_preserving.
    change (subst_cc) with (subst_cc++[]).
    eapply elab_compiler_prefix_implies_elab.
    eapply elab_compiler_prefix_implies_elab.
    constructor.
    eapply elab_preserving_compiler_embed.
    eapply subst_cc_preserving.
    solve_incl.
    eapply elab_preserving_compiler_embed.
    eapply heap_id'_preserving.
    solve_incl.
    solve_incl.
    rewrite <-?app_assoc; solve[prove_from_known_elabs].
    rewrite <-?app_assoc; solve[prove_from_known_elabs].
    apply use_compute_all_fresh; vm_compute; reflexivity.
  }
  {
    eapply elab_preserving_compiler_monotonicity.
    2:eapply elab_preserving_compiler_embed.
    2:eapply fix_cc_preserving.
    change (subst_cc) with (subst_cc++[]).
    repeat eapply elab_compiler_prefix_implies_elab.
    constructor.
    eapply elab_preserving_compiler_embed.
    eapply subst_cc_preserving.
    solve_incl.
    eapply elab_preserving_compiler_embed.
    eapply prod_cc_preserving.
    solve_incl.
    eapply elab_preserving_compiler_embed.
    eapply cc_preserving.
    solve_incl.    
    solve_incl.
    rewrite <-?app_assoc; solve[prove_from_known_elabs].
    rewrite <-?app_assoc; solve[prove_from_known_elabs].
    apply use_compute_all_fresh; vm_compute; reflexivity.
  }
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
