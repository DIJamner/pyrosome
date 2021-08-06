Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Compilers Elab ElabCompilers ElabCompilersWithPrefix.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

Require Coq.derive.Derive.

Lemma elab_preserving_compiler_embed cmp_pre tgt cmp ecmp src tgt'
    : elab_preserving_compiler cmp_pre tgt cmp ecmp src ->
      incl tgt tgt' ->
      elab_preserving_compiler cmp_pre tgt' cmp ecmp src.
Proof.
  induction 1; basic_goal_prep; constructor; basic_core_crush.
  eapply eq_sort_lang_monotonicity; eauto.
  eapply eq_term_lang_monotonicity; eauto.
Qed.
Hint Resolve elab_preserving_compiler_embed : auto_elab.


Lemma strengthen_named_list_lookup {A} (cmp : named_list A) n
  : forall cmp', incl cmp cmp' ->
                 all_fresh cmp' ->
                 In n (map fst cmp) ->
                 named_list_lookup_err cmp' n = named_list_lookup_err cmp n.
Proof.
  induction cmp; basic_goal_prep;  symmetry; basic_utils_crush.
  my_case neq (n =? s); basic_goal_prep; basic_utils_crush.
Qed.

Lemma compile_strengthen_term_incl cmp e
  : all_constructors (fun n => In n (map fst cmp)) e ->
    forall cmp', incl cmp cmp' ->
                 all_fresh cmp' ->
                 compile cmp' e = compile cmp e.
Proof.
  induction e; basic_goal_prep; basic_core_crush.
  erewrite strengthen_named_list_lookup; eauto.
  case_match; basic_goal_prep;[| basic_core_crush].
  case_match; basic_goal_prep;[| basic_core_crush].
  f_equal.
  f_equal.
 
  revert dependent l.
  induction l; basic_goal_prep; f_equal; firstorder.
Qed.

Lemma compile_strengthen_args_incl cmp e
  : all (all_constructors (fun n => In n (map fst cmp))) e ->
    forall cmp', incl cmp cmp' ->
                 all_fresh cmp' ->
                 compile_args cmp' e = compile_args cmp e.
Proof.
  induction e; basic_goal_prep;
    f_equal; firstorder eauto using compile_strengthen_term_incl.
Qed.
Hint Rewrite compile_strengthen_args_incl : lang_core.


Lemma compile_strengthen_sort_incl cmp e
  : all_constructors_sort (fun n => In n (map fst cmp)) e ->
    forall cmp', incl cmp cmp' ->
                 all_fresh cmp' ->
                 compile_sort cmp' e = compile_sort cmp e.
Proof.
  induction e; basic_goal_prep; basic_core_crush.
  erewrite strengthen_named_list_lookup; eauto.
  case_match; basic_goal_prep;[| basic_core_crush].
  case_match; basic_goal_prep;[basic_core_crush|].
  f_equal.
  f_equal.
  apply compile_strengthen_args_incl; eauto.
Qed.


Lemma compile_strengthen_ctx_incl cmp e
  : all_constructors_ctx (fun n => In n (map fst cmp)) e ->
    forall cmp', incl cmp cmp' ->
                 all_fresh cmp' ->
                 compile_ctx cmp' e = compile_ctx cmp e.
Proof.
  induction e; basic_goal_prep;
    f_equal; [f_equal|]; firstorder eauto using compile_strengthen_sort_incl.
Qed.

Fixpoint constructor_names (l:lang) : list string :=
  match l with
  | (n,term_rule _ _ _)::l' => n::(constructor_names l')
  | (n,sort_rule _ _)::l' => n::(constructor_names l')
  | _::l' => constructor_names l'
  |[] => []
  end.

Lemma preserving_compiler_constructor_names tgt cmp src
  : preserving_compiler tgt cmp src ->
    map fst cmp = constructor_names src.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
Qed.

Lemma sort_rule_in_constructor_names n c args l
  : In (n, sort_rule c args) l -> In n (constructor_names l).
Proof.
  induction l; basic_goal_prep; basic_core_crush.
  case_match; basic_core_crush.
Qed.
Hint Resolve sort_rule_in_constructor_names : lang_core.


Lemma term_rule_in_constructor_names n c args t l
  : In (n, term_rule c args t) l -> In n (constructor_names l).
Proof.
  induction l; basic_goal_prep; basic_core_crush.
  case_match; basic_core_crush.
Qed.
Hint Resolve term_rule_in_constructor_names : lang_core.

Local Lemma all_constructors_from_wf src
  : (forall c t,
        wf_sort src c t ->
        all_constructors_sort (fun n0 : string => In n0 (constructor_names src)) t)
    /\ (forall c e t,
           wf_term src c e t ->
           all_constructors (fun n0 : string => In n0 (constructor_names src)) e)
    /\ (forall c s c',
           wf_args src c s c' ->
           all (all_constructors (fun n0 : string => In n0 (constructor_names src))) s).
Proof using.
  intros; apply wf_judge_ind; basic_goal_prep;
    with_rule_in_wf_crush.  
Qed.

Definition all_constructors_sort_from_wf src
  := proj1 (all_constructors_from_wf src).
#[export] Hint Resolve all_constructors_sort_from_wf : lang_core.

Definition all_constructors_term_from_wf src 
  := proj1 (proj2 (all_constructors_from_wf src)).
#[export] Hint Resolve all_constructors_term_from_wf : lang_core.

Definition all_constructors_args_from_wf src
  := proj2 (proj2 (all_constructors_from_wf src)).
#[export] Hint Resolve all_constructors_args_from_wf : lang_core.

Lemma all_constructors_ctx_from_wf src c
  : wf_ctx src c ->
    all_constructors_ctx (fun n0 : string => In n0 (constructor_names src)) c.
Proof.
  induction 1; basic_goal_prep;
    with_rule_in_wf_crush.
Qed.
#[export] Hint Resolve all_constructors_ctx_from_wf : lang_core.

Require Import Compilers.



Lemma strengthen_named_list_lookup' {A} (ecmp cmp : named_list A) n
  : forall cmp', incl cmp cmp' ->
                 all_fresh cmp' ->
                 In n (map fst (ecmp++cmp)) ->
                 named_list_lookup_err (ecmp++cmp') n = named_list_lookup_err (ecmp++cmp) n.
Proof.
  induction ecmp; basic_goal_prep; basic_utils_crush.
  eapply strengthen_named_list_lookup; eauto.
  my_case neq (n =? s); basic_goal_prep; basic_utils_crush.
Qed.


Lemma compile_strengthen_term_incl' ecmp cmp e
  : all_constructors (fun n => In n (map fst (ecmp++cmp))) e ->
    forall cmp', incl cmp cmp' ->
                 all_fresh cmp' ->
                 (compile (ecmp ++ cmp') e) = (compile (ecmp ++ cmp) e).
Proof.
  induction e; basic_goal_prep; basic_core_crush.
  erewrite strengthen_named_list_lookup'; eauto.
  case_match; basic_goal_prep;[| basic_core_crush].
  case_match; basic_goal_prep;[| basic_core_crush].
  f_equal.
  f_equal.
 
  revert dependent l.
  induction l; basic_goal_prep; f_equal; firstorder.
Qed.


Lemma compile_strengthen_args_incl' ecmp cmp e
  : all (all_constructors (fun n => In n (map fst (ecmp++cmp)))) e ->
    forall cmp', incl cmp cmp' ->
                 all_fresh cmp' ->
                 (compile_args (ecmp ++ cmp') e) = (compile_args (ecmp ++ cmp) e).
Proof.
  induction e; basic_goal_prep;
    f_equal; firstorder eauto using compile_strengthen_term_incl'.
Qed.


Lemma compile_strengthen_sort_incl' ecmp cmp e
  : all_constructors_sort (fun n => In n (map fst (ecmp++cmp))) e ->
    forall cmp', incl cmp cmp' ->
                 all_fresh cmp' ->
                 compile_sort (ecmp++cmp') e = compile_sort (ecmp++cmp) e.
Proof.
  induction e; basic_goal_prep; basic_core_crush.
  erewrite strengthen_named_list_lookup'; eauto.
  case_match; basic_goal_prep;[| basic_core_crush].
  case_match; basic_goal_prep;[basic_core_crush|].
  f_equal.
  f_equal.
  apply compile_strengthen_args_incl'; eauto.
Qed.


Lemma compile_strengthen_ctx_incl' ecmp cmp e
  : all_constructors_ctx (fun n => In n (map fst (ecmp++cmp))) e ->
    forall cmp', incl cmp cmp' ->
                 all_fresh cmp' ->
                 compile_ctx (ecmp++cmp') e = compile_ctx (ecmp++cmp) e.
Proof.
  induction e; basic_goal_prep;
    f_equal; [f_equal|]; firstorder eauto using compile_strengthen_sort_incl'.
Qed.

Lemma constructor_names_app l l'
  : constructor_names (l++l') = (constructor_names l) ++ (constructor_names l').
Proof.
  induction l; basic_goal_prep; try case_match; basic_goal_prep; basic_core_crush.
Qed.


Lemma elab_preserving_compiler_monotonicity cmp' cmp_pre tgt cmp ecmp src src_pre cmp_pre'
  : ElabCompilers.elab_preserving_compiler tgt cmp' cmp_pre src_pre ->
    elab_preserving_compiler cmp_pre tgt cmp ecmp src ->
    wf_lang (src++src_pre) ->
    incl cmp_pre cmp_pre' ->
    all_fresh cmp_pre' ->
    elab_preserving_compiler cmp_pre' tgt cmp ecmp src.
Proof.
  induction 2; basic_goal_prep; autorewrite with utils lang_core in *; constructor; intuition eauto.
  {
    erewrite compile_strengthen_ctx_incl'; eauto.
    eapply all_constructors_ctx_weaken; cycle 1.
    basic_core_crush.
    simpl; intro.
    erewrite !preserving_compiler_constructor_names; eauto.
    eapply elab_compiler_implies_preserving.
    eapply elab_compiler_prefix_implies_elab; eauto.
  }
  {
    erewrite compile_strengthen_ctx_incl'; eauto.
    erewrite compile_strengthen_sort_incl'; eauto.
    {
      eapply all_constructors_sort_weaken; cycle 1.
      basic_core_crush.
      simpl; intro.
      erewrite !preserving_compiler_constructor_names; eauto.
      eapply elab_compiler_implies_preserving.
      eapply elab_compiler_prefix_implies_elab; eauto.
    }
    {
      eapply all_constructors_ctx_weaken; cycle 1.
      basic_core_crush.
      simpl; intro.
      erewrite !preserving_compiler_constructor_names; eauto.
      eapply elab_compiler_implies_preserving.
      eapply elab_compiler_prefix_implies_elab; eauto.
    }
  }
  {
    erewrite compile_strengthen_ctx_incl'; eauto.
    erewrite compile_strengthen_sort_incl'; eauto.
    erewrite (compile_strengthen_sort_incl' ecmp t2); eauto.
    {
      eapply all_constructors_sort_weaken; cycle 1.
      basic_core_crush.
      simpl; intro.
      erewrite !preserving_compiler_constructor_names; eauto.
      eapply elab_compiler_implies_preserving.
      eapply elab_compiler_prefix_implies_elab; eauto.
    }
    {
      eapply all_constructors_sort_weaken; cycle 1.
      basic_core_crush.
      simpl; intro.
      erewrite !preserving_compiler_constructor_names; eauto.
      eapply elab_compiler_implies_preserving.
      eapply elab_compiler_prefix_implies_elab; eauto.
    }
    {
      eapply all_constructors_ctx_weaken; cycle 1.
      basic_core_crush.
      simpl; intro.
      erewrite !preserving_compiler_constructor_names; eauto.
      eapply elab_compiler_implies_preserving.
      eapply elab_compiler_prefix_implies_elab; eauto.
    }
  }
  {
    erewrite compile_strengthen_ctx_incl'; eauto.
    erewrite compile_strengthen_sort_incl'; eauto.
    erewrite (compile_strengthen_term_incl' ecmp e1); eauto.
    erewrite (compile_strengthen_term_incl' ecmp e2); eauto.
    {
      eapply all_constructors_term_weaken; cycle 1.
      basic_core_crush.
      simpl; intro.
      erewrite !preserving_compiler_constructor_names; eauto.
      eapply elab_compiler_implies_preserving.
      eapply elab_compiler_prefix_implies_elab; eauto.
    }
    {
      eapply all_constructors_term_weaken; cycle 1.
      basic_core_crush.
      simpl; intro.
      erewrite !preserving_compiler_constructor_names; eauto.
      eapply elab_compiler_implies_preserving.
      eapply elab_compiler_prefix_implies_elab; eauto.
    }
    {
      eapply all_constructors_sort_weaken; cycle 1.
      basic_core_crush.
      simpl; intro.
      erewrite !preserving_compiler_constructor_names; eauto.
      eapply elab_compiler_implies_preserving.
      eapply elab_compiler_prefix_implies_elab; eauto.
    }
    {
      eapply all_constructors_ctx_weaken; cycle 1.
      basic_core_crush.
      simpl; intro.
      erewrite !preserving_compiler_constructor_names; eauto.
      eapply elab_compiler_implies_preserving.
      eapply elab_compiler_prefix_implies_elab; eauto.
    }
  }
Qed.
Hint Resolve elab_preserving_compiler_monotonicity : auto_elab.

Require Import Matches.

   Ltac estep_under lang rule :=
      eredex_steps_with lang rule
      || (compute_eq_compilation; term_cong; (estep_under lang rule|| term_refl)).

    Ltac eredex_steps_with lang name ::=
  let mr := eval vm_compute in (named_list_lookup_err lang name) in
  lazymatch mr with
  | Some (term_eq_rule ?c ?e1p ?e2p ?tp) =>
      lazymatch goal with
      | |- eq_term ?l ?c' ?t ?e1 ?e2 =>
            let s := open_constr:((_ : subst)) in
            (first [ unify_var_names s c | fail 100 "could not unify var names" ]); (first
             [ replace (eq_term l c' t e1 e2) with (eq_term l c' tp [/s /] e1p [/s /] e2p [/s /]);
                [  | f_equal; vm_compute; reflexivity ]
             | fail 2 "could not replace with subst" ]);
             eapply (eq_term_subst (l:=l) (c:=c') (s1:=s) (s2:=s) (c':=c));
             [ try (solve [ cleanup_auto_elab ])
             | eapply eq_subst_refl; try (solve [ cleanup_auto_elab ])
             | eapply (eq_term_by l c name tp e1p e2p); try (solve [ cleanup_auto_elab ]) ]
      end
  | None => fail 100 "rule not found in lang"
  end; repeat t.
    Ltac rewrite_leftwards lang name :=
      first [ eapply eq_term_trans; [estep_under lang name |]
            | eapply eq_term_trans; [|estep_under lang name ]];
      compute_eq_compilation.

    
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
    

  Ltac solve_leaf :=    
    eapply elab_preserving_compiler_embed;
    [ solve[ eauto 1 with elab_pfs auto_elab] | solve_incl].

  Ltac build_compiler_setup :=
  eapply elab_compiler_implies_preserving;
  [repeat eapply elab_compiler_prefix_implies_elab; eauto with elab_pfs auto_elab].

  
  Ltac solve_side_goal :=
    lazymatch goal with
    | [|- wf_lang _] =>
      rewrite <-?app_assoc; solve[prove_from_known_elabs]
    | [|- incl _ _ ] => solve_incl
    | [|- all_fresh _ ] => apply use_compute_all_fresh; vm_compute; reflexivity
    end.

  
  Ltac after_mono :=       
       repeat lazymatch goal with
              | [|-  ElabCompilers.elab_preserving_compiler _ _  (_++_) _] =>
                eapply elab_compiler_prefix_implies_elab
              | [|-  ElabCompilers.elab_preserving_compiler _ _  ?cmp _] =>
                change cmp with (cmp++[]);
                  eapply elab_compiler_prefix_implies_elab;
                  [ solve [ constructor] |]
              end;
       solve_leaf.

  Ltac solve_level2 :=    
    eapply elab_preserving_compiler_monotonicity;
      [|eapply elab_preserving_compiler_embed; [solve_leaf | ..] |..];
      [ after_mono | solve_side_goal ..].

  Ltac build_compiler :=
    build_compiler_setup;
    (solve_leaf || solve_level2).

  
