Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core.
Import Exp.Notations.
(*TODO: rename this to compiler proofs and have a separate export-only file?*)
Require Export CompilerDefs.

Lemma fresh_compile_ctx x cmp c
  : fresh x (compile_ctx cmp c) <-> fresh x c.
Proof.
  induction c; basic_goal_prep;
    basic_core_crush.
Qed.
Hint Rewrite fresh_compile_ctx : lang_core.


Lemma all_fresh_compile_ctx cmp c
  : all_fresh (compile_ctx cmp c) <-> all_fresh c.
Proof.
  induction c; basic_goal_prep;
    basic_core_crush.
Qed.
Hint Rewrite all_fresh_compile_ctx : lang_core.


Lemma fresh_lang_fresh_cmp lt cmp l n
  : preserving_compiler lt cmp l ->
    fresh n l -> fresh n cmp.
Proof.
  induction 1; basic_goal_prep;
    basic_core_crush.
Qed.
#[export] Hint Resolve fresh_lang_fresh_cmp : lang_core.


Lemma all_fresh_compiler lt cmp l
  : preserving_compiler lt cmp l ->
    all_fresh l ->
    all_fresh cmp.
Proof.
  induction 1;
    basic_goal_prep;
    basic_core_crush.
Qed.
#[export] Hint Resolve all_fresh_compiler : lang_core. 


Fixpoint all_constructors P e :=
  match e with
  | var _ => True
  | con n s => P n /\ all (all_constructors P) s
  end.

Definition all_constructors_sort P t :=
  match t with
  | scon n s => P n /\ all (all_constructors P) s
  end.

(*We use a notation so that auto recognizes it after
  reduction
*) 
Notation all_constructors_ctx P c :=
  (all (fun '(_,t) => all_constructors_sort P t) c).

Lemma compile_strengthen_term cmp n cc e
  : fresh n cmp ->
    all_fresh cmp ->
    all_constructors (fun n => In n (map fst cmp)) e ->
    compile ((n,cc)::cmp) e = compile cmp e.
Proof.
  induction e; basic_goal_prep; basic_core_crush.
  my_case Heq (n0 =? n); basic_goal_prep;
    basic_core_crush.
  case_match; basic_goal_prep;
      basic_core_crush.
  case_match; basic_goal_prep;
    basic_core_crush.
  f_equal.
  f_equal.

  revert dependent l.
  induction l; basic_goal_prep; basic_core_crush.
Qed.
Hint Rewrite compile_strengthen_term : lang_core.

Lemma compile_strengthen_args cmp n cc e
  : fresh n cmp ->
    all_fresh cmp ->
    all (all_constructors (fun n => In n (map fst cmp))) e ->
    compile_args ((n,cc)::cmp) e = compile_args cmp e.
Proof.
  induction e; basic_goal_prep; basic_core_crush.
Qed.
Hint Rewrite compile_strengthen_args : lang_core.

Lemma compile_strengthen_sort cmp n cc e
  : fresh n cmp ->
    all_fresh cmp ->
    all_constructors_sort (fun n => In n (map fst cmp)) e ->
    compile_sort ((n,cc)::cmp) e = compile_sort cmp e.
Proof.
  destruct e; basic_goal_prep; basic_core_crush.
  my_case Heq (s =? n); basic_goal_prep;
    basic_core_crush.
  case_match; basic_goal_prep;
      basic_core_crush.
  case_match; basic_goal_prep;
    basic_core_crush.
  f_equal.
  f_equal.
  apply compile_strengthen_args; assumption.
Qed.
Hint Rewrite compile_strengthen_sort : lang_core.


Lemma compile_strengthen_ctx cmp n cc c
  : fresh n cmp ->
    all_fresh cmp ->
    all (fun '(_,t) => all_constructors_sort (fun n => In n (map fst cmp)) t) c ->
    compile_ctx ((n,cc)::cmp) c = compile_ctx cmp c.
Proof.
  induction c; basic_goal_prep; f_equal; basic_core_crush.
Qed.
Hint Rewrite compile_strengthen_ctx : lang_core.

(*
Ltac rewrite_strengthen :=
  match goal with
  | [H : wf_ctx _ _, pr : preserving_compiler _ _ _ |-_] =>
    rewrite (compile_strengthen_ctx _ H pr); eauto with lang_core
  | [H : wf_sort _ _ _, pr : preserving_compiler _ _ _ |-_] =>
    rewrite (compile_strengthen_sort _ H pr); eauto with lang_core
  | [H : wf_term _ _ _ _, pr : preserving_compiler _ _ _ |-_] =>
    rewrite (compile_strengthen_term _ H pr); eauto with lang_core
  end.
*)

(* TODO: work on
Ltac inductive_implies_semantic_rule :=
intros wfl pr wfl';
  revert wfl'; induction pr; simpl; [easy|..];
    repeat (simpl; autorewrite with bool_utils pfcore utils);
    intuition; subst;
      try match goal with
          | [wfl : wf_lang ?l, H: is_true((_,_) \in ?l)|-_] =>
            let H':= fresh in pose proof (rule_in_wf wfl H) as H'; safe_invert H'
          end;
      repeat rewrite_strengthen; [];
  cbn [compile_pf]; 
    repeat (simpl; autorewrite with bool_utils pfcore utils);
  assumption.
*)
  


Lemma sort_name_in_cmp tgt cmp src c' args n
  : preserving_compiler tgt cmp src ->
    In (n, sort_rule c' args) src ->
    In n (map fst cmp).
Proof.
  induction 1;basic_goal_prep;
    with_rule_in_wf_crush.
Qed.
Local Hint Resolve sort_name_in_cmp : lang_core.

Lemma term_name_in_cmp tgt cmp src c' args t n
  : preserving_compiler tgt cmp src ->
    In (n, term_rule c' args t) src ->
    In n (map fst cmp).
Proof.
  induction 1;basic_goal_prep;
    with_rule_in_wf_crush.
Qed.
Local Hint Resolve term_name_in_cmp : lang_core.
                   
Local Lemma all_constructors_from_wf tgt cmp src
  : preserving_compiler tgt cmp src ->
    (forall c t,
        wf_sort src c t ->
        all_constructors_sort (fun n0 : string => In n0 (map fst cmp)) t)
    /\ (forall c e t,
           wf_term src c e t ->
           all_constructors (fun n0 : string => In n0 (map fst cmp)) e)
    /\ (forall c s c',
           wf_args src c s c' ->
           all (all_constructors (fun n0 : string => In n0 (map fst cmp))) s).
Proof using.
  intros; apply wf_judge_ind; basic_goal_prep;
    with_rule_in_wf_crush.
Qed.

Definition all_constructors_sort_from_wf tgt cmp src (pr : preserving_compiler tgt cmp src)
  := proj1 (all_constructors_from_wf pr).
#[export] Hint Resolve all_constructors_sort_from_wf : lang_core.

Definition all_constructors_term_from_wf tgt cmp src (pr : preserving_compiler tgt cmp src)
  := proj1 (proj2 (all_constructors_from_wf pr)).
#[export] Hint Resolve all_constructors_term_from_wf : lang_core.

Definition all_constructors_args_from_wf tgt cmp src (pr : preserving_compiler tgt cmp src)
  := proj2 (proj2 (all_constructors_from_wf pr)).
#[export] Hint Resolve all_constructors_args_from_wf : lang_core.

Lemma all_constructors_ctx_from_wf tgt cmp src c
  : preserving_compiler tgt cmp src ->
    wf_ctx src c ->
    all_constructors_ctx (fun n0 : string => In n0 (map fst cmp)) c.
Proof.
  induction 2; basic_goal_prep;
    with_rule_in_wf_crush.
Qed.
#[export] Hint Resolve all_constructors_ctx_from_wf : lang_core.
                   
Lemma inductive_implies_semantic_sort_axiom ls lt cmp name c t1 t2
  : wf_lang lt -> preserving_compiler lt cmp ls -> wf_lang ls ->
    In (name, sort_eq_rule c t1 t2) ls ->
    eq_sort lt (compile_ctx cmp c) (compile_sort cmp t1) (compile_sort cmp t2).
Proof.
  induction 2;
    basic_goal_prep; try use_rule_in_wf;
      basic_core_crush.
  (*TODO: why is this needed? should be automated*)
  all: use_rule_in_wf;autorewrite with lang_core in *;
    intuition eauto with lang_core.
Qed.


Lemma inductive_implies_semantic_term_axiom ls lt cmp name c e1 e2 t
  : wf_lang lt -> preserving_compiler lt cmp ls -> wf_lang ls ->
    In (name, term_eq_rule c e1 e2 t) ls ->
    eq_term lt (compile_ctx cmp c) (compile_sort cmp t) (compile cmp e1) (compile cmp e2).
Proof.
  induction 2;
    basic_goal_prep;
    try use_rule_in_wf;
    basic_core_crush.
  (*TODO: why is this needed? should be automated*)
  all: use_rule_in_wf;autorewrite with lang_core in *;
    intuition eauto with lang_core.
Qed.


Lemma with_names_from_compile_ctx (A:Set) cmp c (s : list A)
  : with_names_from (compile_ctx cmp c) s
    = with_names_from c s.
Proof.
  revert s; induction c;
    destruct s; break; basic_core_crush.
  cbn.
  f_equal; basic_core_crush.
Qed.
  



Lemma compile_id_args A cmp (c : named_list A)
  : map (compile cmp) (id_args c) = id_args c.
Proof.
  unfold id_args.
  induction c; 
    basic_goal_prep;
    basic_core_crush.
Qed.
Hint Rewrite compile_id_args : lang_core.

Lemma fst_equal_id_args_equal A B (c1 : named_list A) (c2 : named_list B)
  : map fst c1 = map fst c2 -> id_args c1 = id_args c2.
Proof.
  unfold id_args; basic_core_crush.
Qed.

Lemma compile_ctx_fst_equal cmp c
  : map fst (compile_ctx cmp c) = map fst c.
Proof.
  induction c; break; simpl; f_equal; auto.
Qed.
 

Lemma inductive_implies_semantic_sort_rule_id ls lt cmp name c args
  : wf_lang lt -> preserving_compiler lt cmp ls -> wf_lang ls ->
    In (name, sort_rule c args) ls ->
    wf_sort lt (compile_ctx cmp c) (compile_sort cmp (scon name (id_args c))).
Proof.
  intros wfl pr wfl';
    revert wfl'; induction pr;
      basic_goal_prep;
      with_rule_in_wf_crush.
  all: try eapply all_constructors_ctx_from_wf; eauto with lang_core.
  {
    my_case Hname (name =? n);[|case_match]; basic_core_crush.
  }
  {
    use_rule_in_wf; basic_core_crush.
  }
  {
    my_case Hname (name =? n);[|case_match]; basic_core_crush.
  }
  {
    use_rule_in_wf; basic_core_crush.
  }
Qed.



Lemma inductive_implies_semantic_term_rule_id ls lt cmp name c args t
  : wf_lang lt -> preserving_compiler lt cmp ls -> wf_lang ls ->
    In (name, term_rule c args t) ls ->
    wf_term lt (compile_ctx cmp c) (compile cmp (con name (id_args c))) (compile_sort cmp t).
Proof.
  intros wfl pr wfl';
    revert wfl'; induction pr;
      basic_goal_prep;
      try use_rule_in_wf;
      basic_core_crush.
  all: try solve [use_rule_in_wf; basic_core_crush].
  {
    my_case Hname (name =? n);[|case_match]; basic_core_crush.
  }
  {
    my_case Hname (name =? n);[|case_match]; basic_core_crush.
  }
Qed.



Lemma lookup_in_dom s n
  : In n (map fst s) -> In (subst_lookup s n) (map snd s).
Proof.
  induction s;
    basic_goal_prep;
    basic_core_crush.
  case_match; basic_core_crush.
Qed.

(*
Lemma wf_con_id_args_subst' A (c : named_list A) s
  : forall n e, In n (map fst c) ->
                In n (map fst s) ->
                In e (id_args c)[/s/] -> In e (map snd s).
Proof.
  induction c;
    basic_goal_prep;
    basic_core_crush.
  (apply lookup_in_dom; assumption).
  
  
  rewrite IHc.
  unfold args_subst.
*)


Lemma compile_subst_lookup cmp s n
  : compile cmp (subst_lookup s n)
  = subst_lookup (compile_subst cmp s) n.
Proof.
  induction s;
    basic_goal_prep;
    basic_core_crush.
  case_match; basic_core_crush.
Qed.
Hint Rewrite compile_subst_lookup : lang_core.


Lemma combine_subst args l s
  : (combine args l)[/s/] = combine args l[/s/].
Proof.
  revert args.
  induction l;
    destruct args;
    basic_goal_prep;
    basic_core_crush.
Qed.


Lemma lang_compiler_sort_case_args_eq lt cmp ls n c args args' e
  : preserving_compiler lt cmp ls ->
    all_fresh ls ->
    In (n, sort_rule c args) ls ->
    In (n, sort_case args' e) cmp ->
    args' = map fst c.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
  match goal with
    [Hp : preserving_compiler _ _ _,
          H : fresh _ _|-_]=>
    pose proof (fresh_lang_fresh_cmp Hp H)
  end.
  basic_core_crush.
Qed.
#[export] Hint Resolve lang_compiler_sort_case_args_eq : lang_core.

Lemma lang_compiler_term_case_args_eq lt cmp ls n c args args' e t
  : preserving_compiler lt cmp ls ->
    all_fresh ls ->
    In (n, term_rule c args t) ls ->
    In (n, term_case args' e) cmp ->
    args' = map fst c.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
  match goal with
    [Hp : preserving_compiler _ _ _,
          H : fresh _ _|-_]=>
    pose proof (fresh_lang_fresh_cmp Hp H)
  end.
  basic_core_crush.
Qed.
#[export] Hint Resolve lang_compiler_term_case_args_eq : lang_core.


Lemma sort_case_in_preserving_well_scoped tgt cmp src n args t
  : preserving_compiler tgt cmp src ->
    ws_lang tgt ->
    In (n, sort_case args t) cmp ->
    well_scoped args t.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
  erewrite <- compile_ctx_fst_equal.
  eapply wf_sort_implies_ws; eauto; eauto with exp lang_core.
Qed.
#[export] Hint Resolve sort_case_in_preserving_well_scoped : lang_core.


Lemma term_case_in_preserving_well_scoped tgt cmp src n args t
  : preserving_compiler tgt cmp src ->
    ws_lang tgt ->
    In (n, term_case args t) cmp ->
    well_scoped args t.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
  erewrite <- compile_ctx_fst_equal.
  eapply wf_term_implies_ws; eauto; eauto with exp lang_core.
Qed.
#[export] Hint Resolve term_case_in_preserving_well_scoped : lang_core.


Local Lemma distribute_compile_subst tgt cmp src s
  : preserving_compiler tgt cmp src ->
    all_fresh src ->
    ws_lang tgt ->
    (forall c t,
        wf_sort src c t ->
        map fst c = map fst s ->
        compile_sort cmp t[/s/] = (compile_sort cmp t)[/compile_subst cmp s/])
    /\ (forall c e t,
           wf_term src c e t ->
           map fst c = map fst s ->
           compile cmp e[/s/] = (compile cmp e)[/compile_subst cmp s/])
    /\ (forall c s' c',
           wf_args src c s' c' ->
           map fst c = map fst s ->
           compile_args cmp s'[/s/] = (compile_args cmp s')[/compile_subst cmp s/]).
Proof using.
  intros; apply wf_judge_ind; 
    basic_goal_prep;
    basic_core_crush.
  {
    case_match; basic_core_crush.
    case_match; basic_core_crush;
      pose proof (lang_compiler_sort_case_args_eq _ _ _ _ _ H H0 H2 HeqH7);
      basic_core_crush.
    {
      fold_Substable.
      match goal with
        [H : compile_args _ _ = _|-_] =>
        unfold compile_args in H;
          rewrite H
      end.
      rewrite with_names_from_args_subst.
      reflexivity.
    }
  }
  {
    case_match; basic_core_crush.
    case_match; basic_core_crush;
    pose proof (lang_compiler_term_case_args_eq _ _ _ _ _ _ H H0 H2 HeqH7);
      basic_core_crush.
    {
      fold_Substable.
      match goal with
        [H : compile_args _ _ = _|-_] =>
        unfold compile_args in H;
          rewrite H
      end.
      rewrite with_names_from_args_subst.
      reflexivity.
    }
    {
      eapply term_case_in_preserving_well_scoped; eauto; eauto with exp.
    }
  }  
Qed.

Lemma compile_term_subst tgt cmp src s c e t
  : preserving_compiler tgt cmp src ->
    all_fresh src ->
    ws_lang tgt ->
    wf_term src c e t ->
    map fst c = map fst s ->
    compile cmp e[/s/] = (compile cmp e)[/compile_subst cmp s/].
Proof.
  intros; eapply distribute_compile_subst; eassumption.
Qed.
Hint Rewrite compile_term_subst : lang_core.


Lemma compile_sort_subst tgt cmp src s c t
  : preserving_compiler tgt cmp src ->
    all_fresh src ->
    ws_lang tgt ->
    wf_sort src c t ->
    map fst c = map fst s ->
    compile_sort cmp t[/s/] = (compile_sort cmp t)[/compile_subst cmp s/].
Proof.
  intros; eapply distribute_compile_subst; eassumption.
Qed.
Hint Rewrite compile_sort_subst : lang_core.


Lemma compile_args_subst tgt cmp src s c s' c'
  : preserving_compiler tgt cmp src ->
    all_fresh src ->
    ws_lang tgt ->
    wf_args src c s' c' ->
    map fst c = map fst s ->
    compile_args cmp s'[/s/] = (compile_args cmp s')[/compile_subst cmp s/].
Proof.
  intros; eapply distribute_compile_subst; eassumption.
Qed.
Hint Rewrite compile_args_subst : lang_core.

Lemma compile_subst_with_names_from A cmp (c':named_list A) s
  : (compile_subst cmp (with_names_from c' s)) = with_names_from c' (map (compile cmp) s).
Proof.
  unfold compile_subst.
  rewrite <- with_names_from_map_is_named_map.
  reflexivity.
Qed.

Lemma compile_scon cmp args s name t
  : all_fresh cmp ->
    In (name, sort_case args t) cmp ->
    (compile_sort cmp (scon name s)) = t[/(combine args (compile_args cmp s))/].
Proof.
  basic_goal_prep; repeat case_match; basic_core_crush.
  {
    (*TODO: should be automated; how best to do so?*)
    pose proof (in_all_fresh_same _ _ _ _ H H0 HeqH1).
    basic_core_crush.
  }
  {
    (*TODO: should be automated; how best to do so?*)
    pose proof (in_all_fresh_same _ _ _ _ H H0 HeqH1).
    basic_core_crush.
  }
  {
    exfalso.
    (*TODO: why isn't this automated already?*)
    eapply named_list_lookup_none; eauto.
  }
Qed.
  
Lemma lang_compiler_conflict_sort_term lt cmp ls n c args args' e
  : preserving_compiler lt cmp ls ->
    all_fresh ls ->
    In (n, sort_rule c args) ls ->
    In (n, term_case args' e) cmp ->
    False.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
  match goal with
    [Hp : preserving_compiler _ _ _,
          H : fresh _ _|-_]=>
    pose proof (fresh_lang_fresh_cmp Hp H)
  end.
  basic_core_crush.
Qed.
#[export] Hint Resolve lang_compiler_conflict_sort_term : lang_core.

  
Lemma lang_compiler_conflict_term_sort lt cmp ls n c args args' e t
  : preserving_compiler lt cmp ls ->
    all_fresh ls ->
    In (n, term_rule c args t) ls ->
    In (n, sort_case args' e) cmp ->
    False.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
  match goal with
    [Hp : preserving_compiler _ _ _,
          H : fresh _ _|-_]=>
    pose proof (fresh_lang_fresh_cmp Hp H)
  end.
  eauto with utils.
Qed.
#[export] Hint Resolve lang_compiler_conflict_term_sort : lang_core.
  
  
(*TODO: do the same thing for terms*)
Lemma inductive_implies_semantic_sort_rule ls lt cmp name c c' args s
  : wf_lang lt -> preserving_compiler lt cmp ls -> wf_lang ls ->
    In (name, sort_rule c' args) ls ->
    wf_ctx lt (compile_ctx cmp c') ->
    wf_args lt (compile_ctx cmp c) (compile_args cmp s) (compile_ctx cmp c') ->
    wf_sort lt (compile_ctx cmp c) (compile_sort cmp (scon name s)).
Proof.
  intros.
  replace (scon name s) with (scon name (id_args c'))[/(with_names_from c' s)/].
  erewrite compile_sort_subst; try eassumption; eauto with lang_core.
  2:{
    econstructor; [eassumption |].
    basic_core_crush.
  }
  eapply wf_sort_subst_monotonicity; auto.
  {
    eapply inductive_implies_semantic_sort_rule_id; eauto.
  }
  all: basic_core_crush.
  {
    rewrite compile_subst_with_names_from.
    erewrite <- with_names_from_compile_ctx.
    eapply wf_subst_from_wf_args; basic_core_crush.
  }
  {
    pose proof (wf_args_length_eq H4).
    unfold compile_args in H5.
    unfold compile_ctx in H5.
    basic_core_crush.
  }
  {
    simpl; f_equal.
    rewrite wf_con_id_args_subst; basic_core_crush.
    rewrite <- all_fresh_compile_ctx.
    eauto with lang_core.
    pose proof (wf_args_length_eq H4).
    unfold compile_args in H5.
    unfold compile_ctx in H5.
    basic_core_crush.
  }
Qed.

Lemma inductive_implies_semantic_term_rule ls lt cmp name c c' args t s
  : wf_lang lt -> preserving_compiler lt cmp ls -> wf_lang ls ->
    In (name, term_rule c' args t) ls ->
    wf_ctx lt (compile_ctx cmp c') ->
    wf_args lt (compile_ctx cmp c) (compile_args cmp s) (compile_ctx cmp c') ->
    wf_term lt (compile_ctx cmp c) (compile cmp (con name s)) (compile_sort cmp t)[/compile_subst cmp (with_names_from c' s)/].
Proof.
  intros.
  replace (con name s) with (con name (id_args c'))[/(with_names_from c' s)/].
  erewrite compile_term_subst; try eassumption; eauto with lang_core.
  2:{
    econstructor; [eassumption |].
    basic_core_crush.
  }
  eapply wf_term_subst_monotonicity; auto.
  {
    eapply inductive_implies_semantic_term_rule_id; eauto.
  }
  {
    basic_core_crush.
  }
  {
    rewrite compile_subst_with_names_from.
    erewrite <- with_names_from_compile_ctx.
    eapply wf_subst_from_wf_args; basic_core_crush.
  }
  {
    pose proof (wf_args_length_eq H4).
    unfold compile_args in H5.
    unfold compile_ctx in H5.
    basic_core_crush.
  }
  {
    simpl; f_equal.
    fold_Substable.
    rewrite wf_con_id_args_subst; basic_core_crush.
    rewrite <- all_fresh_compile_ctx.
    eauto with lang_core.
    pose proof (wf_args_length_eq H4).
    unfold compile_args in H5.
    unfold compile_ctx in H5.
    basic_core_crush.
  }
Qed.


(*TODO: maybe not necessary with better strengthening lemma?
  See what happens when I use the better one
*)
Variant rule_compiles_with {lt cmp} : rule -> Prop :=
| sort_rule_compiles_with c args
  : wf_ctx lt (compile_ctx cmp c) -> rule_compiles_with (sort_rule c args)
| term_rule_compiles_with c args t
  : wf_ctx lt (compile_ctx cmp c) ->
    wf_sort lt (compile_ctx cmp c) (compile_sort cmp t) ->
    rule_compiles_with (term_rule c args t)
(*Similar properties are not necessary for eq rules*)
| sort_eq_rule_compiles_with c t1 t2 : rule_compiles_with (sort_eq_rule c t1 t2)
| term_eq_rule_compiles_with c e1 e2 t : rule_compiles_with (term_eq_rule c e1 e2 t).
Arguments rule_compiles_with : clear implicits.
                       
Definition lang_compiles_with lt cmp : lang -> Prop :=
  all (fun p => rule_compiles_with lt cmp (snd p)).


Lemma lang_compiles_with_sort_ctx_in lt cmp ls n c' args
  : lang_compiles_with lt cmp ls ->
    In (n, sort_rule c' args) ls ->
    wf_ctx lt (compile_ctx cmp c').
Proof.
  induction ls; 
    basic_goal_prep;
    basic_core_crush.
  (*TODO: This could be automated w/ an inversion lemma*)
  match goal with
    [H : rule_compiles_with _ _ _ |-_]=>
    inversion H; basic_core_crush
  end.
Qed.
Local Hint Resolve lang_compiles_with_sort_ctx_in : lang_core.

Lemma lang_compiles_with_term_ctx_in lt cmp ls n c' args t
  : lang_compiles_with lt cmp ls ->
    In (n, term_rule c' args t) ls ->
    wf_ctx lt (compile_ctx cmp c').
Proof.
  induction ls; 
    basic_goal_prep;
    basic_core_crush.
  (*TODO: This could be automated w/ an inversion lemma*)
  match goal with
    [H : rule_compiles_with _ _ _ |-_]=>
    inversion H; basic_core_crush
  end.
Qed.
Local Hint Resolve lang_compiles_with_term_ctx_in : lang_core.

Lemma lang_compiles_with_term_sort_in lt cmp ls n c' args t
  : lang_compiles_with lt cmp ls ->
    In (n, term_rule c' args t) ls ->
    wf_sort lt (compile_ctx cmp c') (compile_sort cmp t).
Proof.
  induction ls; 
    basic_goal_prep;
    basic_core_crush.
  (*TODO: This could be automated w/ an inversion lemma*)
  match goal with
    [H : rule_compiles_with _ _ _ |-_]=>
    inversion H; basic_core_crush
  end.
Qed.
Local Hint Resolve lang_compiles_with_term_sort_in : lang_core.


Local Lemma inductive_implies_semantic' lt cmp ls
  : wf_lang ls ->
    wf_lang lt ->
    preserving_compiler lt cmp ls ->
    lang_compiles_with lt cmp ls ->
    semantics_preserving lt cmp ls.
Proof.
  intros; apply judge_ind; 
    basic_goal_prep;
    basic_core_crush.
  {
    eapply inductive_implies_semantic_sort_axiom; eassumption.
  }
  {
    erewrite !compile_sort_subst.
    all: try match goal with
               [|- map fst _ = map fst _] =>
               symmetry; eauto with lang_core
             end.
    all: basic_core_crush.
  }
  {
    erewrite !compile_sort_subst.
    erewrite !compile_term_subst.
    all: try match goal with
               [|- map fst _ = map fst _] =>
               symmetry; eauto with lang_core
             end.
    all: basic_core_crush.
  }
  {
    eapply inductive_implies_semantic_term_axiom; eassumption.
  }
  {
    constructor; basic_core_crush.
    match goal with
      [ H : eq_term _ _ (compile_sort _ _) _ _|-_] =>
      erewrite !compile_sort_subst in H
    end.
    all: try match goal with
               [|- map fst _ = map fst _] =>
               symmetry; eauto with lang_core
             end.
    all: basic_core_crush.
  }
  {
    eapply inductive_implies_semantic_sort_rule; try eassumption.
    all: try use_rule_in_wf; basic_core_crush.
  }
  {
    erewrite compile_sort_subst; eauto.
    all: try match goal with
               [|- map fst _ = map fst _] =>
               symmetry; eauto with lang_core
             end.
    all: basic_core_crush.
    assert (wf_ctx ls c') by (use_rule_in_wf; basic_core_crush).
    eapply inductive_implies_semantic_term_rule; try (auto;eassumption).
    all: try use_rule_in_wf; basic_core_crush.
  }
  {
    constructor.
    apply in_named_map; assumption.
  }
  {
    constructor; basic_core_crush.
    match goal with
      [ H : wf_term _ _ _ (compile_sort _ _) |-_] =>
      erewrite !compile_sort_subst in H
    end.
    all: try match goal with
               [|- map fst _ = map fst _] =>
               symmetry; eauto with lang_core
             end.
    all: basic_core_crush.
    match goal with
      [H : context [compile_subst _ (with_names_from _ _)]|-_] =>
      rewrite compile_subst_with_names_from in H
    end.
    rewrite with_names_from_compile_ctx.
    assumption.
  }
Qed.

Local Lemma inductive_implies_semantic_ctx' lt cmp ls
  : wf_lang ls ->
    wf_lang lt ->
    preserving_compiler lt cmp ls ->
    lang_compiles_with lt cmp ls ->
    forall c : ctx, wf_ctx ls c -> wf_ctx lt (compile_ctx cmp c).
Proof.
  intros wfs wft pc lcw.
  apply inductive_implies_semantic'; eauto.
Qed.
Local Hint Resolve inductive_implies_semantic_ctx' : lang_core.


Local Hint Constructors rule_compiles_with : lang_core.

Definition all_constructors_rule P r :=
  match r with
  | sort_rule c _ => all (fun '(_, t) => all_constructors_sort P t) c
  | term_rule c _ t =>
    (all (fun '(_, t) => all_constructors_sort P t) c)
    /\ (all_constructors_sort P t)
  | _ => True
  end.

Local Lemma rule_compiles_extend_fresh lt cmp r n cc
  : rule_compiles_with lt cmp r ->
    all_constructors_rule (fun n0 : string => In n0 (map fst cmp)) r ->
    fresh n cmp ->
    all_fresh cmp ->
    rule_compiles_with lt ((n,cc)::cmp) r.
Proof.
  inversion 1; basic_goal_prep; with_rule_in_wf_crush.
  all: constructor.
  all: try erewrite compile_strengthen_ctx; eauto.
  all: try rewrite compile_strengthen_sort; eauto.
Qed. 
  
Local Lemma lang_compiles_extend_fresh lt cmp ls n cc
  : lang_compiles_with lt cmp ls ->
    all (fun '(_,r) => all_constructors_rule (fun n0 : string => In n0 (map fst cmp)) r) ls ->
    fresh n cmp ->
    all_fresh cmp ->
    lang_compiles_with lt ((n,cc)::cmp) ls.
Proof.
  unfold lang_compiles_with.
  induction ls; basic_goal_prep; with_rule_in_wf_crush.
  eapply rule_compiles_extend_fresh; eauto.
Qed.  

(*TODO: move to core with like lemmas above*)
Lemma all_constructors_rule_from_wf tgt cmp src r
  : preserving_compiler tgt cmp src ->
    wf_rule src r ->
    all_constructors_rule (fun n0 : string => In n0 (map fst cmp)) r.
Proof.
  inversion 2; basic_goal_prep;
    with_rule_in_wf_crush.
  (*TODO: automation; need to restrict simplify?*)
  all: eapply all_constructors_ctx_from_wf; eauto.
Qed.
#[export] Hint Resolve all_constructors_rule_from_wf : lang_core.

Lemma all_constructors_term_weaken (P Q : _ -> Prop) e
  : (forall n, P n -> Q n) ->
    all_constructors P e ->
    all_constructors Q e.
Proof.
  intro.
  induction e; basic_goal_prep; basic_core_crush.

  revert dependent l;
    induction l; basic_goal_prep; basic_core_crush.
Qed.
#[export] Hint Resolve all_constructors_term_weaken : lang_core.


Lemma all_constructors_args_weaken (P Q : _ -> Prop) l
  : (forall n, P n -> Q n) ->
    all (all_constructors P) l ->
    all (all_constructors Q) l.
Proof.
  intro;
    revert dependent l;
    induction l; basic_goal_prep; basic_core_crush.
Qed.
#[export] Hint Resolve all_constructors_args_weaken : lang_core.


Lemma all_constructors_sort_weaken (P Q : _ -> Prop) e
  : (forall n, P n -> Q n) ->
    all_constructors_sort P e ->
    all_constructors_sort Q e.
Proof.
  intro.
  destruct e; basic_goal_prep; basic_core_crush.
Qed.
#[export] Hint Resolve all_constructors_sort_weaken : lang_core.

Lemma all_constructors_ctx_weaken (P Q : _ -> Prop) (c : ctx)
  : (forall n, P n -> Q n) ->
    all_constructors_ctx P c ->
    all_constructors_ctx Q c.
Proof.
  intro;
    induction c; basic_goal_prep; basic_core_crush.
Qed.
#[export] Hint Resolve all_constructors_ctx_weaken : lang_core.


Lemma all_constructors_rule_weaken (P Q : _ -> Prop) r
  : (forall n, P n -> Q n) ->
    all_constructors_rule P r ->
    all_constructors_rule Q r.
Proof.
  intro;
    destruct r; basic_goal_prep; basic_core_crush.
  all: eapply all_constructors_ctx_weaken; eauto.
Qed.
#[export] Hint Resolve all_constructors_rule_weaken : lang_core.


Lemma all_constructors_lang_weaken (P Q : _ -> Prop) (l : lang)
  : (forall n, P n -> Q n) ->
    all (fun '(_, t) => all_constructors_rule P t) l ->
    all (fun '(_, t) => all_constructors_rule Q t) l.
Proof.
  intro;
    induction l; basic_goal_prep; basic_core_crush.
Qed.
#[export] Hint Resolve all_constructors_lang_weaken : lang_core.

Lemma wf_lang_implies_all_constructors lt l
  : wf_lang l ->
    forall cmp,
    preserving_compiler lt cmp l ->
    all (fun '(_,r) => all_constructors_rule (fun n0 : string => In n0 (map fst cmp)) r) l.
Proof.
  induction 1; basic_goal_prep;
    with_rule_in_wf_crush.
  (*TODO: break down cmp*)
  inversion H2; subst.
  1,2:specialize (IHwf_lang cmp0).
  3,4:specialize (IHwf_lang cmp).
  all:eapply all_constructors_lang_weaken.
  all: try apply IHwf_lang; auto.
  all:basic_goal_prep; basic_core_crush.
Qed.


Local Lemma preserving_compiler_to_lang_compiles_with lt ls
  : wf_lang ls ->
    wf_lang lt ->
    forall cmp,
    preserving_compiler lt cmp ls ->
    lang_compiles_with lt cmp ls.
Proof.
  induction 1; inversion 2; basic_goal_prep; with_rule_in_wf_crush.
  all: try constructor.
  all: try rewrite compile_strengthen_ctx; eauto.
  all: try rewrite compile_strengthen_sort; eauto.
  all: try apply lang_compiles_extend_fresh; eauto with lang_core.
  all: try eapply wf_lang_implies_all_constructors; eauto.
  all: eapply all_constructors_ctx_from_wf; [| eauto..]; eauto.
Qed.


Theorem inductive_implies_semantic lt cmp ls
  : wf_lang ls ->
    wf_lang lt ->
    preserving_compiler lt cmp ls ->
    semantics_preserving lt cmp ls.
Proof.
  intros; apply inductive_implies_semantic';
    eauto using  preserving_compiler_to_lang_compiles_with.
Qed.
