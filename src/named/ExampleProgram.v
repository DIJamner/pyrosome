Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Compilers Elab ElabCompilers ElabCompilersWithPrefix
     SimpleVSubst SimpleVCPS SimpleEvalCtx SimpleEvalCtxCPS SimpleUnit NatHeap SimpleVCPSHeap
     SimpleVFixCPS SimpleVCC SimpleVCCHeap SimpleVFix Matches CompilerTransitivity CompilerTools.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.

Ltac solve_incl := 
  solve [auto with utils
        | apply use_compute_incl_lang; vm_compute; reflexivity].
Ltac use_preserving_hint :=
  eapply elab_preserving_compiler_embed;
  [eapply elab_preserving_compiler_monotonicity;
   [ eauto with elab_pfs| solve_incl|apply use_compute_all_fresh; vm_compute; reflexivity]
  | solve_incl].

(*TODO: put these hints with their subjects*)
Hint Resolve cps_preserving : elab_pfs.
Hint Resolve Ectx_cps_preserving : elab_pfs.
Hint Resolve fix_cps_preserving : elab_pfs.

Hint Resolve ElabCompilers.elab_preserving_compiler_nil : auto_elab.

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

Ltac solve_incl ::= 
  solve [auto with utils
        | apply use_compute_incl_compiler; vm_compute; reflexivity
        | apply use_compute_incl_lang; vm_compute; reflexivity].


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
  all: solve [use_preserving_hint].
Qed.  

(*TODO: handle forget discrepancy*)
Lemma full_cc_compiler_preserving
  : preserving_compiler
      (heap_cps_ops ++ heap ++ nat_exp ++ nat_lang
            ++ cc_lang ++ forget_eq_wkn'
            ++ unit_eta ++ unit_lang
            ++ prod_cc ++ cps_prod_lang
            ++ block_subst ++ value_subst)
      (heap_cc++heap_id'++cc++prod_cc_compile++ subst_cc++[])
      (heap_cps_ops++(unit_lang ++ heap ++ nat_exp ++ nat_lang)++cps_lang++cps_prod_lang++(block_subst ++ value_subst)++[]).
Proof.
  eapply elab_compiler_implies_preserving.
  repeat eapply elab_compiler_prefix_implies_elab; eauto with elab_pfs auto_elab.
  
  all: try solve [use_preserving_hint].
  admit.
Admitted.  

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
