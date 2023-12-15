Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Tools.AllConstructors.
Import Core.Notations.
From Pyrosome.Compilers Require Export CompilerDefs.

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
  
  Notation eq_subst l :=
    (eq_subst (Model:= core_model l)).
  Notation eq_args l :=
    (eq_args (Model:= core_model l)).
  Notation wf_subst l :=
    (wf_subst (Model:= core_model l)).
  Notation wf_args l :=
    (wf_args (Model:= core_model l)).
  Notation wf_ctx l :=
    (wf_ctx (Model:= core_model l)).

  Section WithPreModel.
    Context {tgt_term tgt_sort : Type}
            {tgt_Model : @PreModel V tgt_term tgt_sort}
            (*TODO: should I make it so that these aren't necessary?*)
            `{WithDefault tgt_term}
            `{WithDefault tgt_sort}.

    
    Lemma compile_subst_lookup cmp s n
      : compile cmp (subst_lookup s n)
        = Substable.subst_lookup (compile_subst cmp s) n.
    Proof.
      induction s;
        basic_goal_prep;
        basic_core_crush.
      case_match; basic_core_crush.
    Qed.
    Hint Rewrite compile_subst_lookup : lang_core.

    
    Lemma with_names_from_compile_ctx (A:Type) cmp c (s : list A)
      : with_names_from (compile_ctx cmp c) s
        = with_names_from c s.
    Proof.
      revert s; induction c;
        destruct s; break; basic_core_crush.
      cbn.
      f_equal; basic_core_crush.
    Qed.
    
  End WithPreModel.

  Section WithModel.
    Context {tgt_term tgt_sort : Type}
            {tgt_Model : @Model V tgt_term tgt_sort}
            (*TODO: should I make it so that these aren't necessary?*)
            `{WithDefault tgt_term}
            `{WithDefault tgt_sort}.

    Notation compile := (compile (V_Eqb:=V_Eqb) (tgt_Model:=tgt_Model.(premodel))).
    Notation compile_sort :=
      (compile_sort (V_Eqb:=V_Eqb) (tgt_Model:=tgt_Model.(premodel))).
    Notation compile_args :=
      (compile_args (V_Eqb:=V_Eqb) (tgt_Model:=tgt_Model.(premodel))).
    Notation compile_subst :=
      (compile_subst (V_Eqb:=V_Eqb) (tgt_Model:=tgt_Model.(premodel))).
    Notation compile_ctx :=
      (compile_ctx (V_Eqb:=V_Eqb) (tgt_Model:=tgt_Model.(premodel))).

    
    Hint Rewrite compile_subst_lookup : lang_core.

  (* Adds some facts that can be derived from wfness of the language
     for a full compiler (not an extension)
     and are helpful to the proof.
   *)
  Inductive preserving_compiler_plus : compiler _ -> lang -> Prop :=
  | preserving_compiler_nil : preserving_compiler_plus [] []
  | preserving_compiler_sort : forall cmp l n c args t,
      preserving_compiler_plus cmp l ->
      Model.wf_ctx (compile_ctx cmp c) ->
      (* Notable: only uses the previous parts of the compiler on c *)
      Model.wf_sort (compile_ctx cmp c) t ->
      preserving_compiler_plus ((n,sort_case (map fst c) t)::cmp)
                              ((n,sort_rule c args) :: l)
  | preserving_compiler_term : forall cmp l n c args e t,
      preserving_compiler_plus cmp l ->
      Model.wf_ctx (compile_ctx cmp c) ->
      (* Notable: only uses the previous parts of the compiler on c, t *)
      Model.wf_term (compile_ctx cmp c) e (compile_sort cmp t) ->
      preserving_compiler_plus ((n, term_case (map fst c) e)::cmp)
                              ((n,term_rule c args t) :: l)
  | preserving_compiler_sort_eq : forall cmp l n c t1 t2,
      preserving_compiler_plus cmp l ->
      Model.wf_ctx (compile_ctx cmp c) ->
      (* Notable: only uses the previous parts of the compiler on c *)
      Model.eq_sort (compile_ctx cmp c)
              (compile_sort cmp t1)
              (compile_sort cmp t2) ->
      preserving_compiler_plus cmp ((n,sort_eq_rule c t1 t2) :: l)
  | preserving_compiler_term_eq : forall cmp l n c e1 e2 t,
      preserving_compiler_plus cmp l ->
      Model.wf_ctx (compile_ctx cmp c) ->
      (* Notable: only uses the previous parts of the compiler on c *)
      Model.eq_term (compile_ctx cmp c)
              (compile_sort cmp t)
              (compile cmp e1)
              (compile cmp e2) ->
      preserving_compiler_plus cmp ((n,term_eq_rule c e1 e2 t) :: l).

  Lemma invert_preserving_compiler_plus_nil cmp
    : preserving_compiler_plus cmp [] <-> cmp = [].
  Proof. prove_inversion_lemma. Qed.
  Hint Rewrite invert_preserving_compiler_plus_nil : lang_core.

  Lemma invert_preserving_compiler_plus_sort_rule n c args t cmp l
    : preserving_compiler_plus ((n,sort_case (map fst c) t)::cmp)
                               ((n,sort_rule c args) :: l)
      <-> preserving_compiler_plus cmp l /\
            Model.wf_ctx (compile_ctx cmp c) /\
            Model.wf_sort (compile_ctx cmp c) t.
  Proof. prove_inversion_lemma. Qed.
  Hint Rewrite invert_preserving_compiler_plus_sort_rule : lang_core.

  Lemma invert_preserving_compiler_plus_term_rule n c args e t cmp l
    : preserving_compiler_plus ((n,term_case (map fst c) e)::cmp)
                               ((n,term_rule c args t) :: l)
      <-> preserving_compiler_plus cmp l /\
            Model.wf_ctx (compile_ctx cmp c) /\
            Model.wf_term (compile_ctx cmp c) e (compile_sort cmp t).
  Proof. prove_inversion_lemma. Qed.
    Hint Rewrite invert_preserving_compiler_plus_term_rule : lang_core.

    
  Lemma invert_preserving_compiler_plus_sort_eq_rule n c t1 t2 cmp l
    : preserving_compiler_plus cmp ((n,sort_eq_rule c t1 t2) :: l)
      <-> preserving_compiler_plus cmp l /\
            Model.wf_ctx (compile_ctx cmp c) /\
            Model.eq_sort (compile_ctx cmp c)
                          (compile_sort cmp t1)
                          (compile_sort cmp t2).
  Proof. prove_inversion_lemma. Qed.
    Hint Rewrite invert_preserving_compiler_plus_sort_eq_rule : lang_core.
    
  Lemma invert_preserving_compiler_plus_term_eq_rule n c e1 e2 t cmp l
    : preserving_compiler_plus cmp ((n,term_eq_rule c e1 e2 t) :: l)
      <-> preserving_compiler_plus cmp l /\
            Model.wf_ctx (compile_ctx cmp c) /\
            Model.eq_term (compile_ctx cmp c)
                          (compile_sort cmp t)
                          (compile cmp e1)
                          (compile cmp e2).
  Proof. prove_inversion_lemma. Qed.
  Hint Rewrite invert_preserving_compiler_plus_term_eq_rule : lang_core.
  
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


Lemma fresh_lang_fresh_cmp cmp l n
  : preserving_compiler_plus cmp l ->
    fresh n l -> fresh n cmp.
Proof.
  induction 1; basic_goal_prep;
    basic_core_crush.
Qed.
Hint Resolve fresh_lang_fresh_cmp : lang_core.


Lemma all_fresh_compiler cmp l
  : preserving_compiler_plus cmp l ->
    all_fresh l ->
    all_fresh cmp.
Proof.
  induction 1;
    basic_goal_prep;
    basic_core_crush.
Qed.
Hint Resolve all_fresh_compiler : lang_core.

Lemma compile_strengthen_term cmp n cc e
  : fresh n cmp ->
    all_fresh cmp ->
    all_constructors (fun n => In n (map fst cmp)) e ->
    compile ((n,cc)::cmp) e = compile cmp e.
Proof.
  induction e; basic_goal_prep; basic_core_crush.
  my_case Heq (eqb n0 n); basic_goal_prep;
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
  my_case Heq (eqb v n); basic_goal_prep;
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


Lemma sort_name_in_cmp cmp src c' args n
  : preserving_compiler_plus cmp src ->
    In (n, sort_rule c' args) src ->
    In n (map fst cmp).
Proof.
  induction 1;basic_goal_prep;
    with_rule_in_wf_crush.
Qed.
Local Hint Resolve sort_name_in_cmp : lang_core.

Lemma term_name_in_cmp cmp src c' args t n
  : preserving_compiler_plus cmp src ->
    In (n, term_rule c' args t) src ->
    In n (map fst cmp).
Proof.
  induction 1;basic_goal_prep;
    with_rule_in_wf_crush.
Qed.
Local Hint Resolve term_name_in_cmp : lang_core.
                   
Local Lemma all_constructors_from_wf cmp src
  : preserving_compiler_plus cmp src ->
    (forall c t,
        wf_sort src c t ->
        all_constructors_sort (fun n0 : V => In n0 (map fst cmp)) t)
    /\ (forall c e t,
           wf_term src c e t ->
           all_constructors (fun n0 : V => In n0 (map fst cmp)) e)
    /\ (forall c s c',
           wf_args src c s c' ->
           all (all_constructors (fun n0 : V => In n0 (map fst cmp))) s).
Proof.
  intros; apply wf_judge_ind; basic_goal_prep;
    with_rule_in_wf_crush.
Qed.

Definition all_constructors_sort_from_wf cmp src (pr : preserving_compiler_plus cmp src)
  := proj1 (all_constructors_from_wf pr).
Hint Resolve all_constructors_sort_from_wf : lang_core.

Definition all_constructors_term_from_wf cmp src (pr : preserving_compiler_plus cmp src)
  := proj1 (proj2 (all_constructors_from_wf pr)).
Hint Resolve all_constructors_term_from_wf : lang_core.

Definition all_constructors_args_from_wf cmp src (pr : preserving_compiler_plus cmp src)
  := proj2 (proj2 (all_constructors_from_wf pr)).
Hint Resolve all_constructors_args_from_wf : lang_core.

Lemma all_constructors_ctx_from_wf cmp src c
  : preserving_compiler_plus cmp src ->
    wf_ctx src c ->
    all_constructors_ctx (fun n0 : V => In n0 (map fst cmp)) c.
Proof.
  induction 2; basic_goal_prep;
    with_rule_in_wf_crush.
Qed.
Hint Resolve all_constructors_ctx_from_wf : lang_core.

    (*TODO: experimental*)

    (*TODO: move to defs*)
    Definition ws_compiler_case (c : compiler_case V) :=
      match c with
      | sort_case c t =>
          well_scoped (Substable:=sort_substable (PreModel:=tgt_Model.(premodel))) c t
      | term_case c e =>
          well_scoped (Substable:= @substable0_is_substable _ _ (term_substable (PreModel:=tgt_Model.(premodel)))) c e
      end.

    Definition ws_compiler : compiler V -> Prop :=
      all (fun p => ws_compiler_case (snd p)).
    
    Section WithModelOk.
      Context {tgt_Model_ok : Model_ok tgt_Model}.


      (*TODO: generalize proofs to all models
#[export] Hint Resolve eq_subst_subst_monotonicity : lang_core.
#[export] Hint Resolve wf_args_subst_monotonicity : lang_core.
       *)
      (*TODO: Add to Model.v*)
Local Hint Resolve wf_sort_subst_monotonicity : lang_core.
Local Hint Resolve wf_term_subst_monotonicity : lang_core.
Local Hint Resolve wf_sort_implies_ws : lang_core.
      Local Hint Resolve wf_term_implies_ws : lang_core.

      (*TODO: move to Substable*)
      Lemma well_scoped_change_args V' A B `{@Substable0 V' A} `{S : @Substable V' A B} (a:B) args args'
        : well_scoped (Substable := S) args' a ->
          args = args' ->
          well_scoped args a.
      Proof.  
        intros; subst; auto.
      Qed.
      Hint Resolve well_scoped_change_args : term.
      
    Lemma preserving_compiler_ws cmp ls
      : preserving_compiler_plus cmp ls ->
        ws_compiler cmp.
    Proof.
      induction 1; basic_goal_prep; basic_core_crush.
      {
        eapply well_scoped_change_args;
          try typeclasses eauto.
        {
          eapply Model.wf_sort_implies_ws; eauto.
        }
        {
          unfold compile_ctx.
          rewrite named_map_fst_eq.
          reflexivity.
        }
      }
      {
        eapply well_scoped_change_args.
        - typeclasses eauto.
        - eapply Model.wf_term_implies_ws; eauto.
        - unfold compile_ctx.
        rewrite named_map_fst_eq.
        reflexivity.
      }
    Qed.      

      
      Lemma preserving_compiler_tail cmp l' l
        : preserving_compiler_plus cmp (l' ++ l) ->
          exists cmp' cmp_pre,
            cmp = cmp'++ cmp_pre
            /\ (preserving_compiler_plus cmp_pre l).
      Proof.
        revert cmp.
        induction l';
          basic_goal_prep.
        {
          exists [], cmp;
            basic_core_crush.
        }
        {
          inversion H1; clear H1; subst;
          specialize (IHl' _ H6); break; subst.
          1,2: let x1 := open_constr:(_::_) in
               exists x1; eexists; basic_utils_crush.
          all: eexists; eexists; basic_utils_crush.
        }
      Qed.


      (*TODO: move to Utils.v*)
      Lemma map_fst_combine_r_padded {A B} `{WithDefault B} (l1 : list A) (l2 : list B)
        : map fst (combine_r_padded l1 l2) = l1.
      Proof.
        revert l2; induction l1; destruct l2;
          basic_goal_prep; repeat case_match; basic_utils_crush.
      Qed.

      Lemma named_map_combine_r_padded {A B C} `{WithDefault B} `{WithDefault C}
            (l1 : list A) (l2 : list B) (f : B -> C)
        : f default = default ->
          NamedList.named_map f (combine_r_padded l1 l2) = combine_r_padded l1 (map f l2).
      Proof.
        intros; revert l2; induction l1; destruct l2;
          basic_goal_prep; basic_utils_crush.
      Qed.

      
    Lemma combine_r_padded_eq_len {A B} `{WithDefault B} (l1 : list A) (l2 : list B)
      : length l1 = length l2 ->
        combine_r_padded l1 l2 = combine l1 l2.
      Proof.
        revert l2; induction l1; destruct l2;
          basic_goal_prep; repeat case_match; basic_utils_crush.
      Qed.
      
      (*TODO: where to put these?*)
      Context (sort_default_subst : forall s, (default : tgt_sort)[/s/] = (default : tgt_sort)).
      Context (term_default_subst : forall s, (default : tgt_term)[/s/] = (default : tgt_term)).
      
      Local Lemma distribute_compile_subst_term cmp (s : subst) e
        : ws_compiler cmp ->
          all_fresh cmp ->
          well_scoped (map fst s) e ->
          compile cmp e[/s/] = (compile cmp e)[/compile_subst cmp s/].
      Proof.
        induction e.
        {
          simpl.
          (*TODO: wrap subst_var for better rewriting*)
          unfold apply_subst.
          simpl.
          erewrite Substable.subst_var; try typeclasses eauto.
          intros; apply compile_subst_lookup.
        }
        {
          simpl.
          intros.
          case_match; auto.
          case_match; auto.
          erewrite subst_assoc; try typeclasses eauto.
          2:{                                              
            rewrite map_fst_combine_r_padded.
            apply named_list_lookup_err_in in HeqH5.
            exact (in_all _ _ _ H2 HeqH5).
          }
          f_equal.
          unfold subst_cmp.
          rewrite named_map_combine_r_padded.
          {
            f_equal.
            rewrite !map_map.
            revert H4 H3 H2 H1.
            induction l;
              basic_goal_prep; auto;
              autorewrite with utils in *;
              intuition idtac.
          }
          {
            apply term_default_subst.
          }
        }
      Qed.
      Hint Rewrite distribute_compile_subst_term : lang_core.

      Local Lemma distribute_compile_subst_args cmp (s : subst) e
        : ws_compiler cmp ->
          all_fresh cmp ->
          well_scoped (map fst s) e ->
          compile_args cmp e[/s/] = (compile_args cmp e)[/compile_subst cmp s/].
      Proof.
        induction e; auto; basic_goal_prep;
          intuition eauto.
        f_equal; eauto.
        apply distribute_compile_subst_term; eauto.
      Qed.
      Hint Rewrite distribute_compile_subst_args : lang_core.

      Local Lemma distribute_compile_subst_sort cmp (s : subst) t
        : ws_compiler cmp ->
          all_fresh cmp ->
          well_scoped (map fst s) t ->
          compile_sort cmp t[/s/] = (compile_sort cmp t)[/compile_subst cmp s/].
      Proof.
        destruct t.
        {
          simpl.
          intros.
          case_match; auto.
          case_match; auto.
          erewrite subst_assoc; try typeclasses eauto.
          2:{                                              
            rewrite map_fst_combine_r_padded.
            apply named_list_lookup_err_in in HeqH4.
            exact (in_all _ _ _ H1 HeqH4).
          }
          f_equal.
          unfold subst_cmp.
          rewrite named_map_combine_r_padded.
          {
            f_equal.
            rewrite !map_map.
            revert H3 H2 H1.
            induction l;
              basic_goal_prep; auto;
              autorewrite with utils in *;
              intuition idtac.
            apply distribute_compile_subst_term; eauto.
          }
          {
            apply term_default_subst.
          }
        }
      Qed.
      Hint Rewrite distribute_compile_subst_sort : lang_core.

      
      Lemma strengthening cmp' cmp l
        : preserving_compiler_plus cmp l ->
          all_fresh (cmp'++cmp) ->
          (forall c t, wf_sort l c t ->
                        compile_sort (cmp'++cmp) t = compile_sort cmp t)
          /\ (forall c e t, wf_term l c e t ->
                        compile (cmp'++cmp) e = compile cmp e)
          /\ (forall c s c', wf_args l c s c' ->
                        compile_args (cmp'++cmp) s = compile_args cmp s).
      Proof.
        intros; apply wf_judge_ind;
          basic_goal_prep;
          basic_core_crush.
        all: pose proof (all_fresh_tail _ _ ltac:(eassumption)).
        all: repeat case_match; auto;
            autorewrite with utils term lang_core in *; eauto.
        all: basic_utils_crush.
        all: try rewrite all_fresh_named_list_lookup_err_in in HeqH1 by assumption.
        all: try rewrite all_fresh_named_list_lookup_err_in in HeqH7 by assumption.
        all: try (pose proof (in_all_fresh_same _ _ _ _ H2
                                (in_or_app _ _ _ ltac:(eauto)) HeqH7) as H';
                  now inversion H').
        {
          pose proof (in_all_fresh_same _ _ _ _ H2
                        (in_or_app _ _ _ ltac:(eauto)) HeqH7) as H';
            inversion H'; clear H'; subst.
          unfold compile_args in H5; rewrite H5.
          reflexivity.
        }
        {
          exfalso.
          eapply named_list_lookup_none_iff in HeqH1.
          intuition eauto;
            pose proof (sort_name_in_cmp _ _ _ H1 H3).
          apply HeqH1 in H7; auto.
        }
        {
          exfalso.
          eapply named_list_lookup_none_iff in HeqH7.
          pose proof (sort_name_in_cmp _ _ _ H1 H3).
          basic_utils_crush.
        }
       (* {
          exfalso.
          basic_utils_crush.
          eapply named_list_lookup_none_iff in HeqH7.
          intuition eauto;
            pose proof (sort_name_in_cmp _ _ _ H1 H3).
          basic_utils_crush.
        }*)
        {
          pose proof (in_all_fresh_same _ _ _ _ H2
                        (in_or_app _ _ _ ltac:(eauto)) HeqH7) as H';
            inversion H'; clear H'; subst.
          unfold compile_args in H5; rewrite H5.
          reflexivity.
        }
        {
          exfalso.
          eapply named_list_lookup_none_iff in HeqH1.
          intuition eauto;
            pose proof (term_name_in_cmp _ _ _ _ H1 H3).
          apply HeqH1 in H7; auto.
        }
        {
          exfalso.
          eapply named_list_lookup_none_iff in HeqH7.
          pose proof (term_name_in_cmp _ _ _ _ H1 H3).
          basic_utils_crush.
        }
      Qed.

      Lemma strengthening_term cmp' cmp l
        : preserving_compiler_plus cmp l ->
          all_fresh (cmp'++cmp) ->
          forall c e t, wf_term l c e t ->
                        compile (cmp'++cmp) e = compile cmp e.
      Proof.
        intros; eapply strengthening; eauto.
      Qed.
      
      Lemma strengthening_sort cmp' cmp l
        : preserving_compiler_plus cmp l ->
          all_fresh (cmp'++cmp) ->
          forall c t, wf_sort l c t ->
                        compile_sort (cmp'++cmp) t = compile_sort cmp t.
      Proof.
        intros; eapply strengthening; eauto.
      Qed.
      
      Lemma strengthening_args cmp' cmp l
        : preserving_compiler_plus cmp l ->
          all_fresh (cmp'++cmp) ->
          forall c s c', wf_args l c s c' ->
                        compile_args (cmp'++cmp) s = compile_args cmp s.
      Proof.
        intros; eapply strengthening; eauto.
      Qed.
      
      Lemma strengthening_ctx cmp' cmp l
        : preserving_compiler_plus cmp l ->
          all_fresh (cmp'++cmp) ->
          forall c, wf_ctx l c ->
                        compile_ctx (cmp'++cmp) c = compile_ctx cmp c.
      Proof.
        induction 3;
          basic_goal_prep; f_equal; eauto; f_equal;
          eapply strengthening_sort; eauto.
      Qed.

          (*TODO: move up*)
      Hint Resolve preserving_compiler_ws : lang_core.
      
    Lemma preserving_contradiction cmp l n r c
      : preserving_compiler_plus cmp l ->
        all_fresh l ->        
        In (n,r) l ->
        In (n,c) cmp ->
        match r,c with
        | term_rule _ _ _, term_case _ _
        | sort_rule _ _, sort_case _ _ => True
        | _,_ => False
        end.
    Proof.
      induction 1;
        basic_goal_prep;
        repeat case_match;
        subst;
        autorewrite with utils in *;
        try tauto;
        intuition (subst;try congruence; eauto with lang_core).
      all: assert (fresh n cmp) by eauto with lang_core;
        basic_utils_crush.
    Qed.

      Lemma sort_case_in_preserving cmp ls name
        : preserving_compiler_plus cmp ls ->
          wf_lang ls ->
          forall c args t args0,
          In (name, sort_rule c args) ls ->
          In (name, sort_case args0 t) cmp ->
          (args0 = (map fst c)
           /\ Model.wf_ctx (compile_ctx cmp c)
           /\ Model.wf_sort (compile_ctx cmp c) t).
      Proof.
        induction 1;
          basic_goal_prep;
          autorewrite with utils term lang_core in *;
          try assumption;
          try tauto;
          try typeclasses eauto.
        {
          destruct H5; destruct H6; break; subst.
          { now eauto. }
          {
            exfalso.
            eapply fresh_lang_fresh_cmp in H4; eauto.
            exfalso; eauto using pair_fst_in.
          }
          { exfalso; now eauto using pair_fst_in. }
          { now eauto. }
        }
        { clear H5 H6; solve[basic_core_crush]. }
        {          
          autorewrite with utils lang_core term in H4.  
          intuition eauto with lang_core.
          (*TODO: why is this slow?
            clear H5 H6; solve[basic_core_crush]. *)
        }
        {
          eapply all_constructors_ctx_from_wf; eauto.
          autorewrite with utils term model lang_core in *.
          intuition subst; eauto with lang_core.
        }
        {
          (* TODO: why does this take a long time?
          basic_core_crush. *)
          break; subst; try tauto.
          now eauto.
        }
        { clear H5 H6; now basic_core_crush. }
        { clear H5 H6; now basic_core_crush. }
        {
          eapply all_constructors_ctx_from_wf; eauto.
          intuition subst;
            autorewrite with utils lang_core term in *;
            break;
            subst.
          all: try assumption.
          all: try tauto.
          basic_core_crush.
        }
        { break; eauto. }
        { break; eauto. }
      Qed.

      Lemma term_case_in_preserving cmp ls name
        : preserving_compiler_plus cmp ls ->
          wf_lang ls ->
          forall c args args0 e t,
          In (name, term_rule c args t) ls ->
          In (name, term_case args0 e) cmp ->
          (args0 = (map fst c)
           /\ Model.wf_ctx (compile_ctx cmp c)
           /\ Model.wf_term (compile_ctx cmp c) e (compile_sort cmp t)).
      Proof.
        induction 1;
          basic_goal_prep;
          autorewrite with utils term lang_core in *;
          try assumption;
          try tauto.
        {
          break; subst.
          now eauto.
        }
        { clear H5 H6; now basic_core_crush. }
        { clear H5 H6; now basic_core_crush. }
        {
          eapply all_constructors_sort_from_wf; eauto.
          intuition subst;
            autorewrite with utils lang_core term in *;
            break;
            subst.
          all: try assumption.
          all: try tauto.
          use_rule_in_wf.
          basic_core_crush.
        }
        { now basic_core_crush. }
        { now basic_core_crush. }
        {
          eapply all_constructors_ctx_from_wf; eauto.
          intuition subst;
            autorewrite with utils lang_core term in *;
            break;
            subst.
          all: try assumption.
          all: try tauto.
          {
            basic_core_crush.
          }
        }
        {
          destruct H5; destruct H6; break; subst; try tauto.
          {
            exfalso.
            eapply fresh_lang_fresh_cmp; eauto.
            basic_utils_crush.
          }
          {
            exfalso; basic_core_crush.
          }
          {
            eapply IHpreserving_compiler_plus; eauto.
          }
        }
        { now basic_core_crush. }
        { now basic_core_crush. }
        {
          eapply all_constructors_sort_from_wf; eauto.
          intuition subst;
            autorewrite with utils lang_core term in *;
            break;
            subst.
          all: try assumption.
          all: try tauto.
          all: eauto.
          all:use_rule_in_wf;
            basic_core_crush.
        }
        { now basic_core_crush. }
        { now basic_core_crush. }
        {
          eapply all_constructors_ctx_from_wf; eauto.
          intuition subst;
            autorewrite with utils lang_core term in *;
            break;
            subst.
          all: try assumption.
          all: try tauto.
          all: use_rule_in_wf;
            basic_core_crush.
        }
        { break; eauto. }
        { break; eauto. }
      Qed.

      Lemma inductive_implies_semantic' cmp ls
        : wf_lang ls ->
          preserving_compiler_plus cmp ls ->
          semantics_preserving cmp ls.
      Proof.
        intros.
        apply judge_ind;
          basic_goal_prep.
        {
          assert (all_fresh cmp) by basic_core_crush.
          lazymatch goal with
            [ Hin : In _ ?ls,
                Hpres : preserving_compiler_plus _ ?ls,
                  Hlang : wf_lang ?ls |- _] =>
              apply in_split in Hin; break; subst;
              apply wf_lang_tail in Hlang; break; subst;
              apply preserving_compiler_tail in Hpres; break; subst
          end.
          autorewrite with utils lang_core in *.
          break.
          erewrite !strengthening_ctx, !strengthening_sort; eauto.
        }
        {
          autorewrite with utils lang_core in *.
          { eapply Model.eq_sort_subst; eauto. }
          all: basic_core_crush.
        }
        {
          eapply Model.eq_sort_refl; eauto.
        }
        {
          eapply Model.eq_sort_trans; eauto.
        }
        {
          eapply Model.eq_sort_sym; eauto.
        }
        {
          autorewrite with utils lang_core in *.
          { eapply Model.eq_term_subst; eauto. }
          all: basic_core_crush.
        }
        {
          assert (all_fresh cmp) by basic_core_crush.
          lazymatch goal with
            [ Hin : In _ ?ls,
                Hpres : preserving_compiler_plus _ ?ls,
                  Hlang : wf_lang ?ls |- _] =>
              apply in_split in Hin; break; subst;
              apply wf_lang_tail in Hlang; break; subst;
              apply preserving_compiler_tail in Hpres; break; subst
          end.
          autorewrite with utils lang_core in *.
          break.
          erewrite !strengthening_ctx, !strengthening_sort, !strengthening_term; eauto.
        }
        {
          eapply Model.eq_term_refl; eauto.
        }
        {
          eapply Model.eq_term_trans; eauto.
        }
        {
          eapply Model.eq_term_sym; eauto.
        }
        {
          eapply Model.eq_term_conv; eauto.
        }
        {
          constructor.
        }
        {
          autorewrite with model lang_core in *; intuition eauto with lang_core term.
        }
        {
          repeat case_match.
          {
            apply named_list_lookup_err_in in HeqH7.
            pose proof (preserving_contradiction _ _ _ ltac:(eassumption) ltac:(eauto with lang_core) H3 HeqH7)
              as H'; inversion H'.
          }
          {
            assert (all_fresh cmp) by basic_core_crush.
            assert (wf_ctx ls c') by (use_rule_in_wf; basic_core_crush).
            autorewrite with utils in *.
            pose proof (sort_case_in_preserving
                          n  
                          ltac:(eassumption)
                                 ltac:(eassumption)
                                        _ _ _ _                       
                                        ltac:(eassumption)
                                               ltac:(eauto with utils)).
            break; subst.
            eapply Model.wf_sort_subst_monotonicity; cycle 2.
            {
              rewrite combine_r_padded_eq_len.
              {
                rewrite combine_map_fst_is_with_names_from.
                erewrite <- @with_names_from_compile_ctx with (tgt_Model:= tgt_Model.(premodel)).
                eapply @wf_subst_from_wf_args with (Model:= tgt_Model).
                eauto.
              }
              basic_core_crush.
            }
            {
              eapply sort_case_in_preserving; eauto with utils.
            }
            assumption.
          }
          {
            rewrite named_list_lookup_none_iff in HeqH7.

            (*TODO: lost indentation
            TODO: need another conclusion of lemma
              admit (*TODO: same admit as above*).
            } *)
            lazymatch goal with
              [ Hin : In _ ?ls,
                  Hpres : preserving_compiler_plus _ ?ls,
                    Hlang : wf_lang ?ls |- _] =>
                apply in_split in Hin; break; subst;
                apply wf_lang_tail in Hlang; break; subst;
                apply preserving_compiler_tail in Hpres; break; subst
            end.
            inversion H3; subst.
            exfalso; apply HeqH7.
            basic_utils_crush.
          }
        }
        {
          case_match.
          1:case_match.
          {
            autorewrite with utils in *; [| basic_core_crush..].
            pose proof (term_case_in_preserving
                          n  
                          ltac:(eassumption)
                                 ltac:(eassumption)
                                        _ _ _ _ _                     
                                        ltac:(eassumption)
                                               ltac:(eauto with utils)).
            break.
            rewrite distribute_compile_subst_sort;
              [| eauto with lang_core..].
            { rewrite combine_r_padded_eq_len; subst.
              {
                rewrite combine_map_fst_is_with_names_from.
                unfold compile_subst.
                rewrite with_names_from_map_is_named_map.
                eapply Model.wf_term_subst_monotonicity; eauto.
                rewrite <- with_names_from_map_is_named_map.
                erewrite <- @with_names_from_compile_ctx with (tgt_Model:= tgt_Model.(premodel)).
                eapply wf_subst_from_wf_args; eauto.
                eapply H5; eauto.
                use_rule_in_wf; basic_core_crush.
              }
              {
                subst; basic_core_crush.
              }
            }
            {
              rewrite map_fst_with_names_from.
              2:basic_core_crush.
              use_rule_in_wf; basic_core_crush.              
            }
          }
          {
            autorewrite with utils in *.
            pose proof (preserving_contradiction _ _ _
                                                 ltac:(eassumption)
                                                        ltac:(eauto with lang_core)
                                                               ltac:(eassumption)
                                                                      ltac:(eauto with utils)) as H';
              destruct H'.
          }
          {
            rewrite named_list_lookup_none_iff in HeqH7.

            (*TODO: lost indentation
            TODO: need another conclusion of lemma
              admit (*TODO: same admit as above*).
            } *)
            lazymatch goal with
              [ Hin : In _ ?ls,
                  Hpres : preserving_compiler_plus _ ?ls,
                    Hlang : wf_lang ?ls |- _] =>
                apply in_split in Hin; break; subst;
                apply wf_lang_tail in Hlang; break; subst;
                apply preserving_compiler_tail in Hpres; break; subst
            end.
            inversion H3; subst.
            exfalso; apply HeqH7.
            basic_utils_crush.
          }
        }
  {
    eapply Model.wf_term_conv; eauto.
  }
  {
    eapply Model.wf_term_var; eauto.
    unfold compile_ctx.
    basic_utils_crush.
  }
  {
    constructor.
  }
  {
    autorewrite with lang_core in *;
    [| intuition eauto with lang_core term utils..].
    {
      constructor; intuition eauto with lang_core term utils.
      {
        unfold compile_subst in *.
        unfold compile_args.
        rewrite with_names_from_map_is_named_map.
        rewrite with_names_from_compile_ctx.
        assumption.
      }
      basic_core_crush.
    }
    rewrite map_fst_with_names_from.
    2:eauto with utils lang_core.
    safe_invert H8.
    eauto with utils lang_core.
  }
  {
    constructor.
  }
  {
    autorewrite with model utils lang_core in *;
    [| intuition eauto with lang_core term utils..].
    intuition eauto with lang_core term utils.
  }
Qed.

      
      Lemma strengthen_preserving_compiler cmp ls
        : wf_lang ls ->
          preserving_compiler_ext [] cmp ls ->
          preserving_compiler_plus cmp ls.
      Proof.
        intros wfl pc; revert wfl; induction pc;
          basic_goal_prep; constructor;
          autorewrite with utils lang_core in *.
        all: break.
        all: eauto with lang_core utils.
        all: eapply inductive_implies_semantic';
          eauto.
      Qed.

      Theorem inductive_implies_semantic cmp ls
        : wf_lang ls ->
          preserving_compiler_ext [] cmp ls ->
          semantics_preserving cmp ls.
      Proof.
        intros.
        apply inductive_implies_semantic'; auto.
        apply strengthen_preserving_compiler; auto.
      Qed.        

    End WithModelOk.
    End WithModel.
      
End WithVar.


#[export] Hint Rewrite fresh_compile_ctx : lang_core.
#[export] Hint Rewrite all_fresh_compile_ctx : lang_core.
#[export] Hint Resolve fresh_lang_fresh_cmp : lang_core.
#[export] Hint Resolve all_fresh_compiler : lang_core.

#[export] Hint Rewrite compile_strengthen_term : lang_core.
#[export] Hint Rewrite compile_strengthen_args : lang_core.
#[export] Hint Rewrite compile_strengthen_sort : lang_core.
#[export] Hint Rewrite compile_strengthen_ctx : lang_core.


#[export] Hint Resolve all_constructors_sort_from_wf : lang_core.
#[export] Hint Resolve all_constructors_term_from_wf : lang_core.
#[export] Hint Resolve all_constructors_args_from_wf : lang_core.
#[export] Hint Resolve all_constructors_ctx_from_wf : lang_core.
#[export] Hint Rewrite compile_subst_lookup : lang_core.

