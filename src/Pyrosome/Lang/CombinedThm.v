Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Compilers Elab ElabCompilers
     SimpleVSubst SimpleVCPS SimpleEvalCtx SimpleEvalCtxCPS SimpleUnit NatHeap SimpleVCPSHeap
     SimpleVFixCPS SimpleVFixCC SimpleVCC SimpleVSTLC SimpleVCCHeap SimpleVFix Matches CompilerTransitivity CompilerTools.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.


Local Notation compiler_case := (compiler_case string).

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
  all: try typeclasses eauto.
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
  solve [basic_utils_crush
        | eapply use_compute_incl_compiler; vm_compute; reflexivity
        | eapply use_compute_incl_lang; vm_compute; reflexivity].
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
Hint Resolve cps_preserving : elab_pfs.
Hint Resolve Ectx_cps_preserving : elab_pfs.
Hint Resolve fix_cps_preserving : elab_pfs.

Hint Resolve ElabCompilers.elab_preserving_compiler_nil : auto_elab.


Lemma preserving_compiler_embed cmp_pre tgt cmp src tgt'
    : preserving_compiler_ext cmp_pre tgt cmp src ->
      incl tgt tgt' ->
      preserving_compiler_ext cmp_pre tgt' cmp src.
Proof.
  induction 1; basic_goal_prep; constructor; basic_core_firstorder_crush.
  eapply wf_sort_lang_monotonicity; eauto.
  eapply wf_term_lang_monotonicity; eauto.
  eapply eq_sort_lang_monotonicity; eauto.
  eapply eq_term_lang_monotonicity; eauto.
Qed.
Hint Resolve preserving_compiler_embed : auto_elab.

Require Import AllConstructors.

Hint Resolve incl_nil_l : utils.
Lemma incl_map_first {A B} (a b : list (A * B))
  : incl a b ->
    incl (map fst a) (map fst b).
Proof.
  revert b;
    induction a;
    basic_goal_prep;
    basic_utils_crush.
Qed.

Lemma elab_compiler_prefix_implies_elab cmp_pre target cmp src src_pre
    : preserving_compiler_ext [] target cmp_pre src_pre ->
      preserving_compiler_ext cmp_pre target cmp src ->
      preserving_compiler_ext [] target (cmp++cmp_pre) (src++src_pre).
  Proof using.
    induction 2; basic_goal_prep; basic_core_firstorder_crush.
    all: constructor; basic_core_crush.
  Qed.

Lemma preserving_compiler_monotonicity cmp_pre tgt cmp src src_pre cmp_pre'
  : preserving_compiler_ext [] tgt cmp_pre src_pre ->
    preserving_compiler_ext cmp_pre tgt cmp src ->
    wf_lang (src++src_pre) ->
    incl cmp_pre cmp_pre' ->
    all_fresh cmp_pre' ->
    preserving_compiler_ext cmp_pre' tgt cmp src.
Proof.
  induction 2; basic_goal_prep; autorewrite with utils lang_core in *;
    try typeclasses eauto; try constructor; intuition eauto.
  Ltac solve_sort_goal :=
      eapply all_constructors_sort_weaken; [typeclasses eauto|..]; cycle 1;
      [eapply all_constructors_sort_from_wf; eauto|];
      simpl; intro;
      erewrite !preserving_compiler_constructor_names; eauto;
        eapply elab_compiler_prefix_implies_elab; eauto.
  Ltac solve_ctx_goal :=
      eapply all_constructors_ctx_weaken; [typeclasses eauto|..]; cycle 1;
      [eapply all_constructors_ctx_from_wf; eauto|];
      simpl; intro;
      erewrite !preserving_compiler_constructor_names; eauto;
        eapply elab_compiler_prefix_implies_elab; eauto.
  all: erewrite ?compile_strengthen_ctx_incl' by (eauto;solve_ctx_goal); auto.
  all: erewrite ?compile_strengthen_sort_incl' by (eauto;solve_sort_goal); auto.
  all: erewrite ?(compile_strengthen_sort_incl' _ t2) by (eauto;solve_sort_goal); auto.
  Ltac solve_term_goal :=
      eapply all_constructors_term_weaken; [typeclasses eauto|..]; cycle 1;
      [eapply all_constructors_term_from_wf; eauto|];
      simpl; intro;
      erewrite !preserving_compiler_constructor_names; eauto;
        eapply elab_compiler_prefix_implies_elab; eauto.
  erewrite ?compile_strengthen_term_incl' by (eauto;solve_term_goal); auto.
  erewrite (compile_strengthen_term_incl' _ e2) by (eauto;solve_term_goal); auto.
Qed.

  
Lemma compiler_append cmp_pre' lt' cmp' ls' lt cmp ls src_pre'
  : preserving_compiler_ext cmp_pre' lt' cmp' ls' ->
    preserving_compiler_ext [] lt cmp_pre' src_pre' ->
    preserving_compiler_ext [] lt cmp ls ->
    incl lt' lt ->
    incl cmp_pre' cmp ->
    all_fresh cmp ->
    wf_lang (ls' ++ src_pre') ->
    preserving_compiler_ext [] lt (cmp' ++ cmp) (ls' ++ ls).
Proof.
  intros.
  eapply preserving_compiler_embed in H; eauto.
  clear lt' H2.
  eapply elab_compiler_prefix_implies_elab; auto.
  eapply preserving_compiler_monotonicity.
  exact H0.
  all: eauto.
Qed.
  
  
Ltac solve_compiler_lookup :=
  eapply preserving_compiler_embed;
            [ solve[ eapply elab_compiler_implies_preserving; eauto with elab_pfs auto_elab]
            | shelve].
  

Lemma wf_lang_concat l l1 l2
  : wf_lang_ext l l1 ->
    wf_lang_ext (l1 ++ l) l2 ->
    wf_lang_ext l (l2 ++ l1).
Proof.
  induction 2; basic_goal_prep; basic_core_firstorder_crush.
  rewrite <- app_assoc; auto.
Qed.
Hint Resolve wf_lang_concat : lang_core.

(*TODO: this is still a tactic performance bottleneck;
  reduce number of calls to it
 *)
Ltac prove_from_known_elabs ::=
  (*TODO: is this what I want, or something more general?*)
  rewrite <- ?as_nth_tail;
  repeat
    lazymatch goal with
    | |- wf_lang_ext ?l_pre (?l1 ++ ?l2) => apply wf_lang_concat
    | |- wf_lang_ext _ _ => prove_ident_from_known_elabs
    | |- all_fresh _ => apply use_compute_all_fresh; vm_compute; reflexivity
    | |- incl _ _ => simple eapply use_compute_incl_lang; compute; reflexivity
    end.


Ltac build_compiler :=  
  unshelve(repeat (first [apply preserving_compiler_nil
                         | eapply compiler_append
                         | solve_compiler_lookup
                         | shelve]));
  first [apply incl_refl
        |eapply use_compute_all_fresh; compute; reflexivity
        |solve_incl
        |prove_from_known_elabs].


(*TODO: add let*)
Lemma full_cps_compiler_preserving
  : preserving_compiler_ext []
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
Proof.  build_compiler. Qed.


Lemma full_cc_compiler_preserving
  : preserving_compiler_ext [] (fix_cc_lang ++
     heap_cps_ops ++cc_lang ++ forget_eq_wkn ++ unit_eta ++ unit_lang
                                      ++ heap ++ nat_exp ++ nat_lang ++ prod_cc ++
                                      forget_eq_wkn'++
                                      cps_prod_lang ++ block_subst ++ value_subst)
                        (fix_cc++heap_cc++heap_id'++cc++prod_cc_compile++subst_cc++[])
                        (fix_cps_lang++heap_cps_ops++(unit_lang ++ heap ++ nat_exp ++ nat_lang)
                            ++cps_lang++cps_prod_lang++(block_subst ++ value_subst)++[]).
Proof. build_compiler. Qed.



Lemma full_compiler_preserving
  : preserving_compiler_ext [] (fix_cc_lang ++
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
