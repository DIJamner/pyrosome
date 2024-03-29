Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Compilers.SemanticsPreservingDef
  Compilers.Compilers Elab.Elab Elab.ElabCompilers
  Tools.Matches Tools.CompilerTools Compilers.CompilerTransitivity.
From Pyrosome.Lang Require Import SimpleVSubst SimpleVCPS SimpleEvalCtx SimpleEvalCtxCPS
  SimpleUnit NatHeap SimpleVCPSHeap
  SimpleVFixCPS SimpleVFixCC SimpleVCC SimpleVSTLC SimpleVCCHeap SimpleVFix.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.


Local Notation compiler_case := (compiler_case string (tgt_term:=term) (tgt_sort:=sort)).

(*TODO: put in right place*)

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
(*

Lemma elab_preserving_compiler_monotonicity cmp' cmp_pre tgt cmp ecmp src src_pre cmp_pre'
  : elab_preserving_compiler [] tgt cmp' cmp_pre src_pre ->
    elab_preserving_compiler cmp_pre tgt cmp ecmp src ->
    wf_lang (src++src_pre) ->
    incl cmp_pre cmp_pre' ->
    all_fresh cmp_pre' ->
    elab_preserving_compiler cmp_pre' tgt cmp ecmp src.
Proof.

Ltac use_preserving_hint :=
  eapply elab_preserving_compiler_embed;
  [eapply elab_preserving_compiler_monotonicity;[shelve| | shelve |..];
   [ eauto with elab_pfs| solve_incl|apply use_compute_all_fresh; vm_compute; reflexivity]
  | solve_incl].
*)

(*TODO: put these hints with their subjects*)
#[local] Hint Resolve cps_preserving : elab_pfs.
#[local] Hint Resolve Ectx_cps_preserving : elab_pfs.
#[local] Hint Resolve fix_cps_preserving : elab_pfs.

#[local] Hint Resolve ElabCompilers.elab_preserving_compiler_nil : auto_elab.


Lemma preserving_compiler_embed {V} `{Eqb_ok V} `{WithDefault V} cmp_pre (tgt : Rule.lang V) cmp src tgt'
    : preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp src ->
      incl tgt tgt' ->
      preserving_compiler_ext (tgt_Model:=core_model tgt') cmp_pre cmp src.
Proof.
  induction 1; basic_goal_prep; constructor; basic_core_firstorder_crush.
  - eapply wf_sort_lang_monotonicity; eauto.
  - eapply wf_term_lang_monotonicity; eauto.
  - eapply eq_sort_lang_monotonicity; eauto.
  - eapply eq_term_lang_monotonicity; eauto.
Qed.
#[local] Hint Resolve preserving_compiler_embed : auto_elab.

Require Import Pyrosome.Tools.AllConstructors.

#[local] Hint Resolve incl_nil_l : utils.
Lemma incl_map_first {A B} (a b : list (A * B))
  : incl a b ->
    incl (map fst a) (map fst b).
Proof.
  revert b;
    induction a;
    basic_goal_prep;
    basic_utils_crush.
Qed.

Lemma elab_compiler_prefix_implies_elab {V} `{Eqb_ok V} `{WithDefault V} cmp_pre (target : Rule.lang V)
  cmp src src_pre
    : preserving_compiler_ext (tgt_Model:=core_model target) [] cmp_pre src_pre ->
      preserving_compiler_ext (tgt_Model:=core_model target) cmp_pre cmp src ->
      preserving_compiler_ext (tgt_Model:=core_model target) [] (cmp++cmp_pre) (src++src_pre).
  Proof using.
    induction 2; basic_goal_prep; basic_core_firstorder_crush.
    all: constructor; basic_core_crush.
  Qed.

  Lemma preserving_compiler_monotonicity {V} `{Eqb_ok V} `{WithDefault V} cmp_pre
    (tgt : Rule.lang V) cmp src src_pre cmp_pre'
  : preserving_compiler_ext (tgt_Model:=core_model tgt) [] cmp_pre src_pre ->
    preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp src ->
    wf_lang (src++src_pre) ->
    incl cmp_pre cmp_pre' ->
    all_fresh cmp_pre' ->
    preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre' cmp src.
Proof.
  induction 2; basic_goal_prep; autorewrite with utils lang_core in *;
    try typeclasses eauto; try constructor; intuition eauto.
  
  all: unfold Model.wf_sort, Model.wf_term, Model.eq_sort, Model.eq_term, core_model.
  Ltac solve_sort_goal :=
    eapply all_constructors_sort_weaken;
    [typeclasses eauto|typeclasses eauto|..]; cycle 1;
      [eapply all_constructors_sort_from_wf; eauto using core_model |];
      simpl; intro;
      erewrite !preserving_compiler_constructor_names; eauto;
        eapply elab_compiler_prefix_implies_elab; eauto.
  Ltac solve_ctx_goal :=
      eapply all_constructors_ctx_weaken; [typeclasses eauto |typeclasses eauto|..]; cycle 1;
      [eapply all_constructors_ctx_from_wf; eauto using core_model|];
      simpl; intro;
      erewrite !preserving_compiler_constructor_names; eauto;
      eapply elab_compiler_prefix_implies_elab; eauto.
  
  all: erewrite ?compile_strengthen_ctx_incl'
    by (try typeclasses eauto; eauto using core_model;solve_ctx_goal); auto.
  all: erewrite !compile_strengthen_sort_incl' with (cmp':=cmp_pre')
      by (try typeclasses eauto; eauto using core_model;solve_sort_goal); auto.
  Ltac solve_term_goal :=
    eapply all_constructors_term_weaken;
    [typeclasses eauto|typeclasses eauto|..]; cycle 1;
      [eapply all_constructors_term_from_wf; eauto using core_model |];
      simpl; intro;
      erewrite !preserving_compiler_constructor_names; eauto;
    eapply elab_compiler_prefix_implies_elab; eauto.

  erewrite !compile_strengthen_term_incl' with (cmp':=cmp_pre')
      by (try typeclasses eauto; eauto using core_model;solve_term_goal); auto.
Qed.  

  
Lemma compiler_append {V} `{Eqb_ok V} `{WithDefault V}
  cmp_pre' lt' cmp' (ls' : Rule.lang V) lt cmp ls src_pre'
  : preserving_compiler_ext (tgt_Model:=core_model lt') cmp_pre' cmp' ls' ->
    preserving_compiler_ext (tgt_Model:=core_model lt) [] cmp_pre' src_pre' ->
    preserving_compiler_ext (tgt_Model:=core_model lt) [] cmp ls ->
    incl lt' lt ->
    incl cmp_pre' cmp ->
    all_fresh cmp ->
    wf_lang (ls' ++ src_pre') ->
    preserving_compiler_ext (tgt_Model:=core_model lt) [] (cmp' ++ cmp) (ls' ++ ls).
Proof.
  intros.
  eapply preserving_compiler_embed in H2; [| eassumption].
  eapply elab_compiler_prefix_implies_elab; auto.
  eapply preserving_compiler_monotonicity.
  1:exact H3.
  all: eauto.
Qed.
  
  
Ltac solve_compiler_lookup :=
  eapply preserving_compiler_embed;
            [ solve[ eapply elab_compiler_implies_preserving; eauto with elab_pfs auto_elab]
            | shelve].
  

Lemma wf_lang_concat {V} `{Eqb_ok V} `{WithDefault V} (l : Rule.lang V) l1 l2
  : wf_lang_ext l l1 ->
    wf_lang_ext (l1 ++ l) l2 ->
    wf_lang_ext l (l2 ++ l1).
Proof.
  induction 2; basic_goal_prep; basic_core_firstorder_crush.
  rewrite <- app_assoc; auto.
Qed.
#[local] Hint Resolve wf_lang_concat : lang_core.

(*TODO: duplicated; backport above lemma*)
Ltac prove_from_known_elabs :=
  rewrite <- ?as_nth_tail;
   repeat
    lazymatch goal with
    | |- wf_lang_ext ?l_pre (?l1 ++ ?l2) => apply wf_lang_concat
    | |- wf_lang_ext _ [] => apply wf_lang_nil
    | |- wf_lang_ext _ _ => prove_ident_from_known_elabs
    | |- all_fresh _ => compute_all_fresh
    | |- incl _ _ => compute_incl
    end.

Ltac build_compiler :=  
  unshelve(repeat (first [apply preserving_compiler_nil
                         | eapply compiler_append
                         | solve_compiler_lookup
                         | shelve]));
  first [apply incl_refl
        |compute_all_fresh
        |compute_incl
        |prove_from_known_elabs].


(*TODO: add let*)
Lemma full_cps_compiler_preserving
  : preserving_compiler_ext
      (tgt_Model := core_model (heap_cps_ops
         ++ fix_cps_lang
         ++ cps_lang
         ++ cps_prod_lang
         ++ unit_lang
         ++ heap
         ++ nat_exp
         ++ nat_lang
         ++ block_subst
         ++ value_subst))
      []
      (fix_cps++ cps ++ heap_ctx_cps ++ Ectx_cps++ heap_cps++heap_id++cps_subst++[])
      (SimpleVFix.fix_lang++SimpleVSTLC.stlc++ heap_ctx++ eval_ctx++heap_ops++(unit_lang ++ heap ++ nat_exp ++ nat_lang)++(exp_subst ++ value_subst)++[]).
Proof. build_compiler. Qed.


Lemma full_cc_compiler_preserving
  : preserving_compiler_ext
      (tgt_Model := core_model (fix_cc_lang ++
     heap_cps_ops ++cc_lang ++ forget_eq_wkn ++ unit_eta ++ unit_lang
                                      ++ heap ++ nat_exp ++ nat_lang ++ prod_cc ++
                                      forget_eq_wkn'++
                                      cps_prod_lang ++ block_subst ++ value_subst))
      []
                        (fix_cc++heap_cc++heap_id'++cc++prod_cc_compile++subst_cc++[])
                        (fix_cps_lang++heap_cps_ops++(unit_lang ++ heap ++ nat_exp ++ nat_lang)
                            ++cps_lang++cps_prod_lang++(block_subst ++ value_subst)++[]).
Proof. build_compiler. Qed.


(*TODO: compiler transitivity*)
Lemma full_compiler_preserving
  : preserving_compiler_ext
      (tgt_Model := core_model (fix_cc_lang ++
                                     heap_cps_ops ++cc_lang ++ forget_eq_wkn ++ unit_eta ++ unit_lang
                                     ++ heap ++ nat_exp ++ nat_lang ++ prod_cc ++
                                     forget_eq_wkn'++
                                     cps_prod_lang ++ block_subst ++ value_subst))
      []
                        (compile_cmp (fix_cc++heap_cc++heap_id'++cc++prod_cc_compile++subst_cc++[])
                        (fix_cps++ cps ++ heap_ctx_cps ++ Ectx_cps++ heap_cps++heap_id++cps_subst++[]))
      (SimpleVFix.fix_lang++SimpleVSTLC.stlc++ heap_ctx++ eval_ctx++heap_ops++(unit_lang ++ heap ++ nat_exp ++ nat_lang)++(exp_subst ++ value_subst)++[]).
Proof.
  apply preservation_transitivity
        with (ir:=(fix_cps_lang++heap_cps_ops++(unit_lang ++ heap ++ nat_exp ++ nat_lang)
                               ++cps_lang++cps_prod_lang++(block_subst ++ value_subst)++[])).
  all: try (rewrite <-?app_assoc; solve[prove_from_known_elabs]).
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
      (fix_cc_lang ++ heap_cps_ops ++cc_lang ++ forget_eq_wkn ++ unit_eta ++ unit_lang
                   ++ heap ++ nat_exp ++ nat_lang ++ prod_cc ++
                   forget_eq_wkn'++
                   cps_prod_lang ++ block_subst ++ value_subst)
      (compile_cmp (fix_cc++heap_cc++heap_id'++cc++prod_cc_compile++subst_cc++[])
                   (fix_cps++ cps ++ heap_ctx_cps ++ Ectx_cps++ heap_cps++heap_id++cps_subst++[]))
      (SimpleVFix.fix_lang++SimpleVSTLC.stlc++ heap_ctx++ eval_ctx++heap_ops++(unit_lang ++ heap ++ nat_exp ++ nat_lang)++(exp_subst ++ value_subst)++[]).
Proof.
  apply inductive_implies_semantic; try typeclasses eauto;
    eauto using ModelImpls.core_model_ok; try reflexivity.
  1: apply ModelImpls.core_model_ok; try typeclasses eauto.
  1: solve [prove_from_known_elabs].
  1: solve [prove_from_known_elabs].
  apply full_compiler_preserving.
Qed.

Definition full_compiler :=
  (compile_cmp (fix_cc++heap_cc++heap_id'++cc++prod_cc_compile++subst_cc++[])
     (fix_cps++ cps ++ heap_ctx_cps ++ Ectx_cps++ heap_cps++heap_id++cps_subst++[])).

Require Import Pyrosome.Compilers.PartialEval.

Definition compile_fn l c t e :=
  partial_eval _ l (compile_ctx full_compiler c) (compile_sort full_compiler t) 100 (compile full_compiler e).

Lemma full_compiler_with_opt_pres_eq
  (src := (SimpleVFix.fix_lang++SimpleVSTLC.stlc++ heap_ctx++ eval_ctx++heap_ops++(unit_lang ++ heap ++ nat_exp ++ nat_lang)++(exp_subst ++ value_subst)++[]))
  (tgt := (fix_cc_lang ++ heap_cps_ops ++cc_lang ++ forget_eq_wkn ++ unit_eta ++ unit_lang
                   ++ heap ++ nat_exp ++ nat_lang ++ prod_cc ++
                   forget_eq_wkn'++
                   cps_prod_lang ++ block_subst ++ value_subst))
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
  1,3:subst tgt; prove_from_known_elabs.
  {
    eapply eq_term_wf_l; eauto; try typeclasses eauto.
    prove_from_known_elabs.
  }
  {
    eapply eq_term_wf_r; eauto; try typeclasses eauto.
    prove_from_known_elabs.
  }
Qed.
