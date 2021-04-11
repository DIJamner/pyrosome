Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core.
Import Exp.Notations.


(* each element is the image for that constructor or axiom*)
Variant compiler_case :=
 | term_case (args : list string) (e:exp)
 | sort_case (args : list string) (t:sort).
Definition compiler := named_list compiler_case.

Lemma invert_eq_term_case_term_case args args' e e'
  : term_case args e = term_case args' e' <-> args = args' /\ e = e'.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_term_case_term_case : lang_core.

Lemma invert_eq_term_case_sort_case args args' e e'
  : term_case args e = sort_case args' e' <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_term_case_sort_case : lang_core.

Lemma invert_eq_sort_case_term_case args args' e e'
  : sort_case args e = term_case args' e' <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_sort_case_term_case : lang_core.

Lemma invert_eq_sort_case_sort_case args args' e e'
  : sort_case args e = sort_case args' e' <-> args = args' /\ e = e'.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_sort_case_sort_case : lang_core.

Section CompileFn.
  Context (tgt : lang)
          (cmp : compiler)
          (src : lang).

  (* does not use src or tgt, only cmp *)
  Fixpoint compile (e : exp) : exp :=
    match e with
    | var x => var x
    | con n s =>
      (*TODO: return Some and use default typeclass?*)
      let default := con "ERR" [] in
      let arg_terms := map compile s in
      match named_list_lookup_err cmp n with
      | Some (term_case args e) => e[/combine args arg_terms/]
      | _ => default
      end
    end.
  
  (* does not use src or tgt, only cmp *)
  Definition compile_sort (t : sort) : sort :=
    match t with
    | scon n s =>
      (*TODO: return Some and use default typeclass?*)
      let default := scon "ERR" [] in
      let arg_terms := map compile s in
      match named_list_lookup_err cmp n with
      | Some (sort_case args t) => t[/combine args arg_terms/]
      | _ => default
      end
    end.  
  
  Definition compile_args := map compile.

  Definition compile_subst (s : named_list exp) := named_map compile s.

  Definition compile_ctx (c:named_list sort) := named_map compile_sort c.

   (* First we specify the properties semantically,
     then inductively on the compiler. TODO: prove equivalent
   *)
  Definition sort_wf_preserving_sem :=
    forall c t, wf_sort src c t ->
                wf_sort tgt (compile_ctx c) (compile_sort t).

  Definition term_wf_preserving_sem :=
    forall c e t,
      wf_term src c e t ->
      wf_term tgt (compile_ctx c) (compile e) (compile_sort t).

  Definition sort_eq_preserving_sem :=
    forall c t1 t2,
      eq_sort src c t1 t2 ->
      eq_sort tgt (compile_ctx c) (compile_sort t1) (compile_sort t2).
  
  Definition term_eq_preserving_sem :=
    forall c t e1 e2,
      eq_term src c t e1 e2 ->
      eq_term tgt (compile_ctx c) (compile_sort t) (compile e1) (compile e2).

  Definition args_wf_preserving_sem :=
    forall c s c',
      wf_args src c s c' ->
      wf_args tgt (compile_ctx c) (compile_args s) (compile_ctx c').

  Definition subst_eq_preserving_sem :=
    forall c c' s1 s2,
      eq_subst src c c' s1 s2 ->
      eq_subst tgt (compile_ctx c) (compile_ctx c') (compile_subst s1) (compile_subst s2).
   
  Definition ctx_wf_preserving_sem :=
    forall c, wf_ctx src c -> wf_ctx tgt (compile_ctx c).

  (*Set up to match the combined scheme for the judgment inductives *)
  Definition semantics_preserving :=
    sort_eq_preserving_sem /\ term_eq_preserving_sem /\ subst_eq_preserving_sem
    /\ sort_wf_preserving_sem /\ term_wf_preserving_sem /\ args_wf_preserving_sem
    /\ ctx_wf_preserving_sem.

End CompileFn.

(*
First we define an inductively provable (and in fact decidable) property 
of elaborated compilers.
*)

(*TODO: this is an equal or stronger property (which?); includes le principles;
  formalize the relationship to those above and le semantic statements *)
Inductive preserving_compiler (target : lang) : compiler -> lang -> Prop :=
| preserving_compiler_nil : preserving_compiler target [] []
| preserving_compiler_sort : forall cmp l n c args t,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    wf_sort target (compile_ctx cmp c) t ->
    preserving_compiler target ((n,sort_case (map fst c) t)::cmp) ((n,sort_rule c args) :: l)
| preserving_compiler_term : forall cmp l n c args e t,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c, t *)
    wf_term target (compile_ctx cmp c) e (compile_sort cmp t) ->
    preserving_compiler target ((n, term_case (map fst c) e)::cmp) ((n,term_rule c args t) :: l)
| preserving_compiler_sort_eq : forall cmp l n c t1 t2,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    eq_sort target (compile_ctx cmp c) (compile_sort cmp t1) (compile_sort cmp t2) ->
    preserving_compiler target cmp ((n,sort_eq_rule c t1 t2) :: l)
| preserving_compiler_term_eq : forall cmp l n c e1 e2 t,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    eq_term target (compile_ctx cmp c) (compile_sort cmp t) (compile cmp e1) (compile cmp e2) ->
    preserving_compiler target cmp ((n,term_eq_rule c e1 e2 t) :: l).


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
Hint Resolve fresh_lang_fresh_cmp : lang_core.


Lemma all_fresh_compiler lt cmp l
  : preserving_compiler lt cmp l ->
    all_fresh l ->
    all_fresh cmp.
Proof.
  induction 1;
    basic_goal_prep;
    basic_core_crush.
Qed.
Hint Resolve all_fresh_compiler : lang_core. 

(*TODO: move to Core*)
Scheme wf_sort_ind' := Minimality for wf_sort Sort Prop
  with wf_term_ind' := Minimality for wf_term Sort Prop
  with wf_args_ind' := Minimality for wf_args Sort Prop.
Combined Scheme wf_judge_ind
         from wf_sort_ind', wf_term_ind', wf_args_ind'.

Local Lemma compile_strengthen tgt cmp src n cc
  : preserving_compiler tgt cmp src ->
    all_fresh src ->
    fresh n src ->
    (forall c t,
        wf_sort src c t ->
        compile_sort ((n,cc)::cmp) t = compile_sort cmp t)
    /\ (forall c e t,
           wf_term src c e t ->
           compile ((n,cc)::cmp) e = compile cmp e)
    /\ (forall c s c',
           wf_args src c s c' ->
           compile_args ((n,cc)::cmp) s = compile_args cmp s).
Proof using.
  intros.
  apply wf_judge_ind; basic_goal_prep; basic_core_crush.
  {
    my_case Heq (n0 =?n); basic_goal_prep;
      basic_core_crush.
    case_match; basic_goal_prep;
      basic_core_crush.
    case_match; basic_goal_prep;
      basic_core_crush.
  }
  {
    my_case Heq (n0 =?n); basic_goal_prep;
      basic_core_crush.
    case_match; basic_goal_prep;
      basic_core_crush.
    case_match; basic_goal_prep;
      basic_core_crush.
  }   
Qed.

Lemma compile_strengthen_term src tgt cmp c e t n cc
  : wf_term src c e t ->
    preserving_compiler tgt cmp src ->
    all_fresh src ->
    fresh n src ->
    compile ((n,cc)::cmp) e = compile cmp e.
Proof.
  intros; eapply compile_strengthen; eauto.
Qed.

Lemma compile_strengthen_sort src tgt cmp c t n cc
  : wf_sort src c t ->
    preserving_compiler tgt cmp src ->
    all_fresh src ->
    fresh n src ->
    compile_sort ((n,cc)::cmp) t = compile_sort cmp t.
Proof.
  intros; eapply compile_strengthen; eauto.
Qed.
Local Hint Resolve compile_strengthen_sort : lang_core.

Lemma compile_strengthen_ctx src tgt cmp c n cc
  : wf_ctx src c ->
    preserving_compiler tgt cmp src ->
    all_fresh src ->
    fresh n src ->
    compile_ctx ((n,cc)::cmp) c = compile_ctx cmp c.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
Qed.


Ltac rewrite_strengthen :=
  match goal with
  | [H : wf_ctx _ _, pr : preserving_compiler _ _ _ |-_] =>
    rewrite (compile_strengthen_ctx _ H pr); eauto with lang_core
  | [H : wf_sort _ _ _, pr : preserving_compiler _ _ _ |-_] =>
    rewrite (compile_strengthen_sort _ H pr); eauto with lang_core
  | [H : wf_term _ _ _ _, pr : preserving_compiler _ _ _ |-_] =>
    rewrite (compile_strengthen_term _ H pr); eauto with lang_core
  end.

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
  

(*TODO: come up w/ a more systematic way of constructing this*)
Ltac with_rule_in_wf_crush :=
  let rewrite_tac := autorewrite with utils exp lang_core in * in
  let hint_auto := eauto with utils exp lang_core in
          subst; rewrite_tac; firstorder;
                   try use_rule_in_wf; rewrite_tac;
  firstorder (subst; rewrite_tac; repeat rewrite_strengthen; hint_auto;
              try (solve [ exfalso; hint_auto
                         | repeat (f_equal; hint_auto)])).


Lemma inductive_implies_semantic_sort_axiom ls lt cmp name c t1 t2
  : wf_lang lt -> preserving_compiler lt cmp ls -> wf_lang ls ->
    In (name, sort_eq_rule c t1 t2) ls ->
    eq_sort lt (compile_ctx cmp c) (compile_sort cmp t1) (compile_sort cmp t2).
Proof.
  induction 2;
    basic_goal_prep;
    with_rule_in_wf_crush.
Qed.


Lemma inductive_implies_semantic_term_axiom ls lt cmp name c e1 e2 t
  : wf_lang lt -> preserving_compiler lt cmp ls -> wf_lang ls ->
    In (name, term_eq_rule c e1 e2 t) ls ->
    eq_term lt (compile_ctx cmp c) (compile_sort cmp t) (compile cmp e1) (compile cmp e2).
Proof.
  induction 2;
    basic_goal_prep;
    with_rule_in_wf_crush.
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


Lemma strengthen_fresh_name A n e (c' : named_list A) s
  : fresh n c' ->
    (map var (map fst c'))[/(n, e) :: s/]
    = (map var (map fst c'))[/s/].
Proof.
  induction c'; 
    basic_goal_prep; auto.
  case_match; basic_utils_crush.
Qed.
  
Lemma wf_con_id_args_subst A (c' : named_list A) s
  : all_fresh c' ->
    length c' = length s ->
    (id_args c')[/with_names_from c' s/] = s.
Proof.
  revert s.
  induction c'; destruct s;
      basic_goal_prep; try f_equal;
        with_rule_in_wf_crush.
  rewrite strengthen_fresh_name; auto.
Qed.
Hint Rewrite wf_con_id_args_subst : lang_core.

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
  pose proof (fresh_lang_fresh_cmp H H1).
  exfalso.
  eauto with utils.
Qed.
Hint Resolve lang_compiler_sort_case_args_eq : lang_core.

Lemma lang_compiler_term_case_args_eq lt cmp ls n c args args' e t
  : preserving_compiler lt cmp ls ->
    all_fresh ls ->
    In (n, term_rule c args t) ls ->
    In (n, term_case args' e) cmp ->
    args' = map fst c.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
  pose proof (fresh_lang_fresh_cmp H H1).
  exfalso.
  eauto with utils.
Qed.
Hint Resolve lang_compiler_term_case_args_eq : lang_core.


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
Hint Resolve sort_case_in_preserving_well_scoped : lang_core.


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
Hint Resolve term_case_in_preserving_well_scoped : lang_core.


(*TODO: move to utils*)
Lemma named_map_length A B (f : A -> B) l
  : length (named_map f l) = length l.
Proof.
  induction l; basic_goal_prep; basic_utils_crush.
Qed.
Hint Rewrite named_map_length : utils.
Hint Rewrite map_length : utils.

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
      unfold compile_args in H4.
      rewrite H4.
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
      unfold compile_args in H4.
      rewrite H4.
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
  unfold compile_subst. Locate with_names_from_map_is_named_map.
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

(*TODO: move to utils*)
Lemma fresh_notin A n (a:A) l
  : fresh n l -> ~In (n,a) l.
Proof.
  unfold fresh.
  intuition eauto using pair_fst_in.
Qed.
Hint Resolve fresh_notin : utils.
  
Lemma lang_compiler_conflict_sort_term lt cmp ls n c args args' e
  : preserving_compiler lt cmp ls ->
    all_fresh ls ->
    In (n, sort_rule c args) ls ->
    In (n, term_case args' e) cmp ->
    False.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
  pose proof (fresh_lang_fresh_cmp H H1).
  eauto with utils.
Qed.
Hint Resolve lang_compiler_conflict_sort_term : lang_core.


  
Lemma lang_compiler_conflict_term_sort lt cmp ls n c args args' e t
  : preserving_compiler lt cmp ls ->
    all_fresh ls ->
    In (n, term_rule c args t) ls ->
    In (n, sort_case args' e) cmp ->
    False.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
  pose proof (fresh_lang_fresh_cmp H H1).
  eauto with utils.
Qed.
Hint Resolve lang_compiler_conflict_term_sort : lang_core.
  
  
(*TODO: do the same thing for terms*)
Lemma inductive_implies_semantic_sort_rule ls lt cmp name c c' args s
  : wf_lang lt -> preserving_compiler lt cmp ls -> wf_lang ls ->
    In (name, sort_rule c' args) ls ->
    (*wf_args ls c s c' ->*)
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

(*
Lemma term_eq_in_lang_proof_in_compiler name lt cmp ls c e1 e2 t
  : preserving_compiler lt cmp ls ->
    (name, wf_term_eq c e1 e2 t) \in ls ->
    exists p, (name, ax_case p) \in cmp.
Proof.
  induction 1; 
    repeat (simpl; autorewrite with bool_utils pfcore utils); eauto with pfcore.
  all: intuition.
  all: try match goal with [H : exists _,_|-_] => destruct H end.
  all: try solve[exists x; 
    repeat (simpl; autorewrite with bool_utils pfcore utils); by eauto with pfcore].
  exists eeq;
    repeat (simpl; autorewrite with bool_utils pfcore utils); by eauto with pfcore.
  Unshelve.
  exact (ax "").
Qed.
*)

Theorem inductive_implies_semantic lt cmp ls
  : wf_lang ls -> wf_lang lt -> preserving_compiler lt cmp ls ->
    semantics_preserving lt cmp ls.
Proof.
  intros; apply judge_ind; 
    basic_goal_prep;
    basic_core_crush.
  {
    eapply inductive_implies_semantic_sort_axiom; eassumption.
  }
  {
    erewrite !compile_sort_subst; eauto.
    basic_core_crush.
    all: admit (*simple side conditions*).
  }
  {
    (*TODO: same for terms
    erewrite !compile_term_subst; eauto.
    basic_core_crush.*)
    admit.
  }
  {
    eapply inductive_implies_semantic_term_axiom; eassumption.
  }
  {
    admit (*TODO*).
  }
  {
    eapply inductive_implies_semantic_sort_rule; try eassumption.
    (*TODO: figure out whether this is necessary/ add it  to lemma if so*)
    admit.
  }  
Abort.

