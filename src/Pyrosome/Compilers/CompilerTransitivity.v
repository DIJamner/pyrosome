Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Theory.ModelImpls Compilers.Compilers.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

 
Section WithVar.
  Context (V : Type)
    {V_Eqb : Eqb V}
    {V_Eqb_ok : Eqb_ok V_Eqb}
    {V_default : WithDefault V}.

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).
  Notation compiler_case := (compiler_case V (tgt_term:=term) (tgt_sort:=sort)).
  Notation compiler := (compiler V (tgt_term:=term) (tgt_sort:=sort)).
  Notation compile := (compile (V:=V) (tgt_term:=term) (tgt_sort:=sort)
                         (tgt_Model:=syntax_model (V:=V))).
  Notation compile_subst := (compile_subst (V:=V) (tgt_term:=term) (tgt_sort:=sort) (tgt_Model:=syntax_model (V:=V))).
  Notation compile_ctx := (compile_ctx (V:=V) (tgt_term:=term) (tgt_sort:=sort) (tgt_Model:=syntax_model (V:=V))).
  Notation compile_args := (compile_args (V:=V) (tgt_term:=term) (tgt_sort:=sort) (tgt_Model:=syntax_model (V:=V))).
  Notation compile_sort := (compile_sort (V:=V) (tgt_term:=term) (tgt_sort:=sort) (tgt_Model:=syntax_model (V:=V))).
  
Lemma compile_subst_combine (cmp : compiler) args s
  : compile_subst cmp (combine args s) = combine args (map (compile cmp) s).
Proof.
  revert args; induction s; destruct args; basic_goal_prep; basic_core_crush.
Qed.

Section CompileFn.
  Context (cmp : compiler).

  Definition compile_ccase (c : compiler_case) :=
    match c with
    | sort_case args t => sort_case args (compile_sort cmp t)
    | term_case args e => term_case args (compile cmp e)
    end.

  Definition compile_cmp (c: compiler) := named_map compile_ccase c.

  Lemma lookup_cmp_distributes cmp' n
    : named_list_lookup_err (compile_cmp cmp') n
      = option_map compile_ccase (named_list_lookup_err cmp' n).
  Proof.
    induction cmp'; basic_goal_prep; basic_core_firstorder_crush.
    case_match; basic_core_crush.
  Qed.
  Hint Rewrite lookup_cmp_distributes : lang_core.
  
  Fixpoint term_in_cmp_domain e :=
    match e with
    | var _ => True
    | con n s =>
      (exists args e, In (n,term_case args e) cmp /\ length args = length s) /\
      all term_in_cmp_domain s
    end.

  Definition sort_in_cmp_domain t :=
    match t with
    | scon n s =>
      (exists args e, In (n,sort_case args e) cmp /\ length args = length s) /\
      all term_in_cmp_domain s
    end.
    
End CompileFn.


(*TODO: move to utils*)
Lemma all_fresh_named_map A B l (f : A -> B)
  : all_fresh (named_map f l) <-> all_fresh l.
Proof.
  induction l; basic_goal_prep; basic_utils_crush.
Qed.
Hint Rewrite all_fresh_named_map : utils.

(*TODO: move to utils*)
Lemma map_fst_combine A B (l1 : list A) (l2 : list B)
  : length l1 = length l2 ->
    map fst (combine l1 l2) = l1.
Proof.
  revert l2; induction l1; destruct l2;
    basic_goal_prep;
    basic_utils_crush.
Qed.
Hint Rewrite map_fst_combine : utils.


(*TODO: move to utils*)
Lemma named_map_combine A B (f : A -> B) l1 l2
  : named_map f (combine l1 l2) = combine l1 (map f l2).
Proof.
  revert l2; induction l1; destruct l2;
    basic_goal_prep;
    basic_utils_crush.
Qed.
Hint Rewrite named_map_combine : utils.

(*TODO: move to Compilers.v*)
Definition ws_ccase (cc : compiler_case) :=
  match cc with
  | term_case args e => well_scoped args e
  | sort_case args e => well_scoped args e
  end.


Lemma in_ws_term_cmp n args e cmp
  : all ws_ccase (map snd cmp) ->
    In (n:V, term_case args e) cmp ->
    well_scoped args e.
Proof.
  induction cmp; basic_goal_prep; basic_core_firstorder_crush.
Qed.


Lemma in_ws_sort_cmp n args e cmp
  : all ws_ccase (map snd cmp) ->
    In (n:V, sort_case args e) cmp ->
    well_scoped args e.
Proof.
  induction cmp; basic_goal_prep; basic_core_firstorder_crush.
Qed.

(*TODO: replace Compilers.v versions with these;
  might help with inductive_implies_semantic last induction?
 *)

Lemma compile_term_subst (cmp : compiler) e s
  : all_fresh cmp ->
    all ws_ccase (map snd cmp) ->
    term_in_cmp_domain cmp e ->
    well_scoped (map fst s) e ->
    compile cmp e[/s/] = (compile cmp e)[/compile_subst cmp s/].
Proof.
  intros allfcmp all_ws.
  induction e; basic_goal_prep; basic_core_firstorder_crush.
  case_match; simpl; eauto.
  apply named_list_lookup_err_in in HeqH4.
  pose proof (in_all_fresh_same _ _ _ _ allfcmp H0 HeqH4).
  subst.

  erewrite subst_assoc.
  2: typeclasses eauto.
  2:{
    rewrite map_fst_combine_r_padded.
    eapply in_ws_term_cmp; eauto.
  }
  f_equal.
  unfold subst_cmp.
  rewrite named_map_combine_r_padded; [|reflexivity].
  f_equal.

  (*prove inner induction*)
  clear x x0 H0 H2 HeqH4.
  revert dependent l.
  induction l; basic_goal_prep; basic_core_crush.
Qed.
Hint Rewrite compile_term_subst : lang_core.


Lemma compile_args_subst cmp e s
  : all_fresh cmp ->
    all ws_ccase (map snd cmp) ->
    all (term_in_cmp_domain cmp) e ->
    well_scoped (map fst s) e ->
    compile_args cmp e[/s/] = (compile_args cmp e)[/compile_subst cmp s/].
Proof.
  induction e; basic_goal_prep; basic_core_crush.
  fold_Substable.
  basic_core_crush.
Qed.

Lemma compile_sort_subst cmp e s
  : all_fresh cmp ->
    all ws_ccase (map snd cmp) ->
    sort_in_cmp_domain cmp e ->
    well_scoped (map fst s) e ->
    compile_sort cmp e[/s/] = (compile_sort cmp e)[/compile_subst cmp s/].
Proof.
  intros allfcmp all_ws.
  induction e; basic_goal_prep; basic_core_firstorder_crush.
  case_match; simpl; eauto.
  apply named_list_lookup_err_in in HeqH3.
  pose proof (in_all_fresh_same _ _ _ _ allfcmp H HeqH3).
  subst.

  erewrite subst_assoc; try typeclasses eauto.
  2:{
    rewrite map_fst_combine_r_padded.
    eapply in_ws_sort_cmp; eauto.
  }
  f_equal.
  unfold subst_cmp.
  rewrite named_map_combine_r_padded.
  {
    f_equal.
    apply compile_args_subst; eauto.
  }
  reflexivity.
Qed.
Hint Rewrite compile_sort_subst : lang_core.

Definition ccase_in_cmp_domain (cmp : compiler) (cc : compiler_case) :=
  match cc with
  | term_case _ e => term_in_cmp_domain cmp e
  | sort_case _ e => sort_in_cmp_domain cmp e
  end.

(* TODO: move to utils*)
Lemma pair_in_map_snd {A B} (a:A) (b:B) l
  : In (a,b) l -> In b (map snd l).
Proof.
  induction l; basic_goal_prep; basic_utils_crush.
Qed.
Hint Resolve pair_in_map_snd : utils.


Lemma compile_cmp_distributes cmp cmp' e
  : 
  (*TODO: find a better way to discharge this*)
  compile cmp default = default ->
  all ws_ccase (map snd cmp) ->
    all_fresh cmp ->
    all ws_ccase (map snd cmp') ->
    all_fresh cmp' ->
    all (ccase_in_cmp_domain cmp) (map snd cmp') ->
    term_in_cmp_domain cmp' e ->
    (compile (compile_cmp cmp cmp') e)
    = (compile cmp (compile cmp' e)).
Proof.
  intros all_ws_cmp allfr_cmp all_ws_cmp' allfr_cmp' cmp'_in_dom.
  induction e; basic_goal_prep; basic_core_firstorder_crush.
  assert (Some (term_case x x0) = named_list_lookup_err cmp' n).
  {
    rewrite all_fresh_named_list_lookup_err_in; eauto.
  }
  rewrite <- H4.
  assert (Some (term_case x (compile cmp x0))
          = named_list_lookup_err (compile_cmp cmp cmp') n).
  {
    rewrite all_fresh_named_list_lookup_err_in.
    2: unfold compile_cmp; basic_utils_crush.
    {
      rewrite all_fresh_named_list_lookup_err_in in H4; eauto.
      unfold compile_cmp.
      change (term_case x (compile cmp x0))
        with (compile_ccase cmp (term_case x x0)).
      eapply in_named_map; eauto.
    }
    unfold compile_cmp; basic_core_crush.
  }
  rewrite <- H5.
  erewrite compile_term_subst; unfold ws_lang;eauto.

  {
    f_equal.
    unfold compile_subst.
    autorewrite with utils.
    rewrite named_map_combine_r_padded; auto.
    f_equal.
    

    (*nested induction*)
    clear x x0 H1 H2 H4 H5.
    revert dependent l.
    induction l; basic_goal_prep; basic_core_crush.
  }
  {
    assert  (ccase_in_cmp_domain cmp (term_case x x0)).
    {
      eapply in_all; eauto.
      eauto with utils.
    }
    repeat autorewrite with utils; auto.
  }
  rewrite map_fst_combine_r_padded.
  eapply in_ws_term_cmp; [|eauto]; eauto.
  
Qed.
Hint Rewrite compile_cmp_distributes : lang_core.


Lemma compile_args_cmp_distributes cmp cmp' e
  :  (*TODO: find a better way to discharge this*)
  compile cmp default = default ->
  all ws_ccase (map snd cmp) ->
    all_fresh cmp ->
    all ws_ccase (map snd cmp') ->
    all_fresh cmp' ->
    all (ccase_in_cmp_domain cmp) (map snd cmp') ->
    all (term_in_cmp_domain cmp') e ->
    (compile_args (compile_cmp cmp cmp') e)
    = (compile_args cmp (compile_args cmp' e)).
Proof.
  intros all_ws_cmp allfr_cmp all_ws_cmp' allfr_cmp' cmp'_in_dom.
  induction e; basic_goal_prep; basic_core_crush.
Qed.
Hint Rewrite compile_args_cmp_distributes : lang_core.


Lemma compile_sort_cmp_distributes cmp cmp' e
  :   (*TODO: find a better way to discharge this*)
  compile cmp default = default ->
  all ws_ccase (map snd cmp) ->
    all_fresh cmp ->
    all ws_ccase (map snd cmp') ->
    all_fresh cmp' ->
    all (ccase_in_cmp_domain cmp) (map snd cmp') ->
    sort_in_cmp_domain cmp' e ->
    (compile_sort (compile_cmp cmp cmp') e)
    = (compile_sort cmp (compile_sort cmp' e)).
Proof.
  intros all_ws_cmp allfr_cmp all_ws_cmp' allfr_cmp' cmp'_in_dom.
  destruct e; basic_goal_prep; basic_core_firstorder_crush.
  assert (Some (sort_case x x0) = named_list_lookup_err cmp' v).
  {
    rewrite all_fresh_named_list_lookup_err_in; eauto.
  }
  rewrite <- H3.
  assert (Some (sort_case x (compile_sort cmp x0))
          = named_list_lookup_err (compile_cmp cmp cmp') v).
  {
    rewrite all_fresh_named_list_lookup_err_in.
    2: unfold compile_cmp; basic_utils_crush.
    {
      rewrite all_fresh_named_list_lookup_err_in in H3; eauto.
      unfold compile_cmp.
      change (sort_case x (compile_sort cmp x0))
        with (compile_ccase cmp (sort_case x x0)).
      eapply in_named_map; eauto.
    }
    unfold compile_cmp; basic_core_crush.
  }
  rewrite <- H4.
  erewrite compile_sort_subst; unfold ws_lang;eauto.

  {
    f_equal.
    unfold compile_subst.
    rewrite named_map_combine_r_padded.
    {
      f_equal.    

      (*nested induction*)
      clear x x0 H1 H0 H3 H4.
      revert dependent l.
      induction l; basic_goal_prep; basic_core_crush.
    }
    now auto.
  }
  {
    assert  (ccase_in_cmp_domain cmp (sort_case x x0)).
    {
      eapply in_all; eauto.
      eauto with utils.
    }
    repeat autorewrite with utils; auto.
  }
  rewrite map_fst_combine_r_padded.
  repeat autorewrite with utils; auto.
  eapply in_ws_sort_cmp; [|eauto]; eauto.
Qed.
Hint Rewrite compile_sort_cmp_distributes : lang_core.


Lemma compile_ctx_cmp_distributes cmp cmp' e
  :   (*TODO: find a better way to discharge this*)
  compile cmp default = default ->
  all ws_ccase (map snd cmp) ->
    all_fresh cmp ->
    all ws_ccase (map snd cmp') ->
    all_fresh cmp' ->
    all (ccase_in_cmp_domain cmp) (map snd cmp') ->
    all (sort_in_cmp_domain cmp') (map snd e) ->
    (compile_ctx (compile_cmp cmp cmp') e)
    = (compile_ctx cmp (compile_ctx cmp' e)).
Proof.
  intros all_ws_cmp allfr_cmp all_ws_cmp' allfr_cmp' cmp'_in_dom.
  induction e; basic_goal_prep; basic_core_crush.
Qed.
Hint Rewrite compile_ctx_cmp_distributes : lang_core.   


Lemma preserving_is_well_scoped cmp_pre tgt cmp ir
  : ws_lang tgt ->
    preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp ir ->
    all ws_ccase (map snd cmp).
Proof.
  induction 2; basic_goal_prep; intuition;
    replace (map fst c) with (map fst (compile_ctx (cmp++cmp_pre) c)).
  - eapply wf_sort_implies_ws; eauto.
  - apply named_map_fst_eq; eauto.
  - eapply wf_term_implies_ws; eauto.
  - apply named_map_fst_eq; eauto.
Qed.
Hint Resolve preserving_is_well_scoped : lang_core.


Lemma sort_in_preserving_lang_in_cmp cmp_pre tgt cmp src n c' args
  : preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp src ->
    In (n, sort_rule c' args) src ->
    exists t, In (n, sort_case (map fst c') t) cmp.
Proof.
  induction 1; basic_goal_prep;
    basic_core_crush.
Qed.

Lemma term_in_preserving_lang_in_cmp cmp_pre tgt cmp src n c' args t
  : preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp src ->
    In (n, term_rule c' args t) src ->
    exists e, In (n, term_case (map fst c') e) cmp.
Proof.
  induction 1; basic_goal_prep;
    basic_core_crush.
Qed.



Lemma wf_in_domain cmp_pre tgt cmp src
  : preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp src ->    
    (forall c t,
        wf_sort src c t ->
        sort_in_cmp_domain cmp t)
    /\ (forall c e t,
           wf_term src c e t ->
           term_in_cmp_domain cmp e)
    /\ (forall c s' c',
           wf_args (Model:=core_model src) c s' c' ->
           all (term_in_cmp_domain cmp) s').
Proof.
  intro pres_cmp.
  apply wf_judge_ind; basic_goal_prep;
    basic_core_firstorder_crush.
  {
    pose proof (sort_in_preserving_lang_in_cmp _ _ _ pres_cmp H).
    firstorder.
    exists (map fst c').
    exists x.
    basic_core_crush.
  }
  {
    pose proof (term_in_preserving_lang_in_cmp _ _ _ _ pres_cmp H).
    firstorder.
    exists (map fst c').
    exists x.
    basic_core_crush.
  }
Qed.

  
Lemma wf_term_in_domain cmp_pre tgt cmp ir c e t
  : preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp ir ->
    wf_term ir c e t ->
    term_in_cmp_domain cmp e.
Proof.
  intros; eapply wf_in_domain; eauto.
Qed.
Hint Resolve wf_term_in_domain : lang_core.

Lemma wf_sort_in_domain cmp_pre tgt cmp ir c t
  : preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp ir ->
    wf_sort ir c t ->
    sort_in_cmp_domain cmp t.
Proof.
  intros; eapply wf_in_domain; eauto.
Qed.
Hint Resolve wf_sort_in_domain : lang_core.

Lemma wf_ctx_in_domain cmp_pre tgt cmp ir c
  : preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp ir ->
    wf_ctx (Model:= core_model ir) c ->
    all (sort_in_cmp_domain cmp) (map snd c).
Proof.
  induction 2; basic_goal_prep; basic_core_crush.
Qed.
Hint Resolve wf_ctx_in_domain : lang_core.
  
Lemma preserving_in_domain cmp_pre tgt cmp ir cmp' src
  : preserving_compiler_ext (tgt_Model:=core_model tgt) cmp_pre cmp ir ->
    preserving_compiler_ext (tgt_Model:=core_model ir ) [] cmp' src ->
    all (ccase_in_cmp_domain cmp) (map snd cmp').
Proof.
  intro pres_cmp.
  induction 1; basic_goal_prep; intuition.
  - eapply wf_sort_in_domain; eauto.
  - eapply wf_term_in_domain; eauto.
Qed.
Hint Resolve preserving_in_domain : lang_core.


Lemma compiler_map_fst_incl tgt cmp l
  : preserving_compiler_ext (tgt_Model:=core_model tgt) [] cmp l ->
    incl (map fst cmp) (map fst l).
Proof.
  induction 1;
    basic_goal_prep;
    basic_core_crush.
Qed.

(*
Lemma all_fresh_incl {A B} (cmp : @Utils.named_list V A) (l : @Utils.named_list V B)
  : incl (map fst cmp) (map fst l) ->
    all_fresh l ->
    all_fresh cmp.
Proof.
  revert cmp.
  induction l;
    basic_goal_prep;
    basic_core_crush.
  {
    destruct cmp; simpl in *; auto.
    inversion H.
  }
  {
    eapply IHl; auto.
  }
  all_fresh_conflict_impossible
    all_fresh_in_once
Qed.*)

Lemma all_fresh_compiler tgt cmp l
  : preserving_compiler_ext (tgt_Model:=core_model tgt) [] cmp l ->
    all_fresh l ->
    all_fresh cmp.
Proof.
  induction 1;
    basic_goal_prep;
    basic_core_crush.
  {
    unfold fresh in *.
    intro; apply H2.
    eapply compiler_map_fst_incl; eauto.
  }
  {
    unfold fresh in *.
    intro; apply H2.
    eapply compiler_map_fst_incl; eauto.
  }
Qed.
Hint Resolve all_fresh_compiler : lang_core.
  
(*TODO: can cmp be generalized w/ a cmp_pre?*)
Theorem preservation_transitivity src ir tgt cmp cmp'
  :  (*TODO: find a better way to discharge this*)
  compile cmp default = default ->
 wf_lang src ->
    wf_lang ir ->
    wf_lang tgt ->
    (forall s : @Substable.subst V (Term.term V),
  @eq (Term.sort V)
    (@apply_subst V (Term.term V) (Term.sort V) (sort_substable (PreModel:=syntax_model (V:=V))) s
       (default)) (default)) ->
    (forall s : @Substable.subst V (Term.term V),
  @eq (Term.term V)
    (@apply_subst0 V (Term.term V) (term_substable (PreModel:=syntax_model (V:=V))) s
       (default)) (default)) ->
    preserving_compiler_ext (tgt_Model:=core_model tgt) [] cmp ir ->
    preserving_compiler_ext (tgt_Model:=core_model ir) [] cmp' src ->
    preserving_compiler_ext (tgt_Model:=core_model tgt) [] (compile_cmp cmp cmp') src.
Proof using V_Eqb_ok.
  intros compile_default wfsrc wfir wftgt sub_default sub_default' pres_cmp pres_cmp'.
  pose proof (inductive_implies_semantic (tgt_Model_ok := core_model_ok wftgt)
                sub_default sub_default' wfir pres_cmp).
  firstorder.
  revert wfsrc.
  induction pres_cmp'; basic_goal_prep; constructor.
  all: rewrite ?invert_wf_lang_cons in *; break; rewrite app_nil_r in *.
  all: eauto.
  all:  erewrite ?compile_ctx_cmp_distributes, ?compile_sort_cmp_distributes, ?compile_cmp_distributes.
  all: eauto with lang_core.
  all: pose proof (core_model_ok wfir).
  all: try (pose proof pres_cmp' as H'; apply inductive_implies_semantic in H').
  all: try typeclasses eauto.
  all: try reflexivity.
  all: try assumption.
  all: autorewrite with lang_core model term utils in *.
  all: break.
  all: try intuition eauto with lang_core model utils.
  all: cbn [Model.eq_sort Model.eq_term Model.wf_sort Model.wf_term core_model] in *.
  1: apply H2; eauto.
  2: apply H3; eauto.
  3: apply H; eauto.
  4: apply H0; eauto.
  all: apply H'; eauto.
Qed.
Hint Resolve preservation_transitivity : lang_core.

End WithVar.

#[export] Hint Rewrite lookup_cmp_distributes : lang_core.
#[export] Hint Rewrite all_fresh_named_map : utils.
#[export] Hint Rewrite map_fst_combine : utils.
#[export] Hint Rewrite named_map_combine : utils.
#[export] Hint Rewrite compile_term_subst : lang_core.
#[export] Hint Rewrite compile_sort_subst : lang_core.
#[export] Hint Resolve pair_in_map_snd : utils.
#[export] Hint Rewrite compile_cmp_distributes : lang_core.
#[export] Hint Rewrite compile_args_cmp_distributes : lang_core.
#[export] Hint Rewrite compile_sort_cmp_distributes : lang_core.
#[export] Hint Rewrite compile_ctx_cmp_distributes : lang_core.   
#[export] Hint Resolve preserving_is_well_scoped : lang_core.
#[export] Hint Resolve wf_term_in_domain : lang_core.
#[export] Hint Resolve wf_sort_in_domain : lang_core.
#[export] Hint Resolve wf_ctx_in_domain : lang_core.
#[export] Hint Resolve preserving_in_domain : lang_core.
#[export] Hint Resolve preservation_transitivity : lang_core.
