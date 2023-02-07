Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Require Import Bool.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Infinite Monad.
From Pyrosome Require Import Theory.Core Theory.Renaming Compilers.CompilerDefs.
Import Core.Notations.

(*TODO: move to Utils.v*)
Definition unique_proofs P := forall (a b : P), a = b.

Lemma is_true_unique : forall b, unique_proofs (Is_true b).
Proof.
  destruct b; intros a b;
    destruct a; destruct b;
    auto.
Qed.

Notation "'{B' x & c }" :=
  (sigT (fun x => Is_true c))
    (x binder, format "'[' '{B'  x  &  c } ']'").


Lemma is_true_subset_eq {A} f (a b : {B x : A & f x})
  : a = b <-> projT1 a = projT1 b.
Proof.
  destruct a; destruct b; simpl;
    intuition try congruence; subst.
  f_equal.
  apply is_true_unique.
Qed.

(*TODO: move to Monad.v *)
Definition named_list_Mmap {M V A B} `{Monad M} (f : A -> M B)
  : @named_list V A -> M (@named_list V B) :=
  list_Mmap (fun '(x,a) => @! let b <- f a in ret (x,b)).

Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
          {V_default : WithDefault V}
  (*{V_inf : Infinite V}*).
  

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

  Section WithParameter.

    (*TODO: how to handle p_name freshness?
      idea: non-identity injective endofunction
      - skip p_name in cod
      - preserve lang vars (w/out proof they are in the lang)
     *)
    Context (p_name : V)
      (p_sort : sort)
      (* assume a renaming where p_name isn't in the codomain *)
      (f : V -> V)
      (*TODO: make Injective a typeclass?*)
      {f_inj : Injective f}
      {p_name_fresh : forall x, f x <> p_name}.

    Lemma p_name_freshb x : Is_true (negb (eqb (f x) p_name)).
    Proof.
      apply negb_prop_intro.
      intro H.
      apply p_name_fresh with (x:=x).
      revert H; unfold Is_true; case_match;
        basic_utils_crush.
    Qed.
    
    (*TODO: move to Renaming?*)
    Definition f' x : {B x & negb (eqb x p_name)} :=
      existT _ (f x) (p_name_freshb x).
    
    Fixpoint parameterize_term (e : term) : term :=
      match e with
      | var x => var x
      | con n s =>
          let s' := map parameterize_term s in
          con n (s'++[var p_name])
      end.
    
    Definition parameterize_sort (e : sort) : sort :=
      match e with
      | scon n s =>
          let s' := map parameterize_term s in
          scon n (s'++[var p_name])
      end.

    (*TODO: double-check when delta should be added.
          E.G. sort w/ parametric arg must be parameterized
          simple sort should not
     *)
    Definition parameterize_ctx (c : ctx) : ctx :=
      (named_map parameterize_sort c)++[(p_name, p_sort)].

    Definition parameterize_sub s :=
      (named_map parameterize_term s)++[(p_name, var p_name)].
    
    Definition parameterize_args s :=
      (map parameterize_term s)++[var p_name].

    Definition parameterize_rule (r : rule) : rule :=
      match r with
      | sort_rule c args =>
          (*TODO: making p implicit in terms but not args is heuristic.
                Give the user more control.
           *)
          sort_rule (parameterize_ctx c) (args++[p_name])
      | term_rule c args t =>
          term_rule (parameterize_ctx c) args (parameterize_sort t)
      | sort_eq_rule c t1 t2 =>
          sort_eq_rule (parameterize_ctx c)
            (parameterize_sort t1)
            (parameterize_sort t2)
      | term_eq_rule c e1 e2 t =>
          term_eq_rule (parameterize_ctx c)
            (parameterize_term e1)
            (parameterize_term e2)
            (parameterize_sort t)
      end.

    
    Definition parameterize_ccase (c : compiler_case V) : compiler_case V :=
      match c with
      | sort_case args t =>
          sort_case (args++[p_name]) (parameterize_sort t)
      | term_case args e =>
          term_case (args++[p_name]) (parameterize_term e)
      end.

    Definition parameterize_compiler : _ -> compiler V :=
      named_map parameterize_ccase.

    Notation parameterize_lang := (named_map parameterize_rule).

    
    Lemma parameterize_subst_lookup s n e
      : n <> p_name ->
        parameterize_term (subst_lookup s n) =
          subst_lookup (named_map parameterize_term s ++ [(p_name, e)]) n.
    Proof.
      intro.
      induction s;
        basic_goal_prep;
        basic_term_crush.
      {
        apply eqb_neq in H.
        rewrite H.
        reflexivity.
      }
      {
        case_match; auto.
      }
    Qed.

    Lemma subst_lookup_p_name s
      : fresh p_name s ->
        subst_lookup (parameterize_sub s) p_name = var p_name.
    Proof.
      induction s;
        basic_goal_prep;
        basic_term_crush.
      {
        case_match;
          basic_utils_crush.
      }
    Qed.

    
    Lemma p_name_not_in_map l
      :  ~ In p_name (map f l).
    Proof.
      induction l;
        basic_goal_prep;
        basic_utils_crush.
    Qed.        
      
    Lemma p_name_fresh_in_subst s
      : fresh p_name (rename_subst f s).
    Proof.
      unfold rename_subst, fresh.
      rewrite map_map; simpl.
      rewrite <- map_map.
      apply p_name_not_in_map.
    Qed.

    Lemma p_name_fresh_in_ctx s
      : fresh p_name (rename_ctx f s).
    Proof.
      unfold rename_ctx, fresh.
      rewrite map_map; simpl.
      rewrite <- map_map.
      apply p_name_not_in_map.
    Qed.


    
    Lemma parameterize_term_subst e s
      : parameterize_term (rename f e) [/rename_subst f s /]
        = (parameterize_term (rename f e)) [/parameterize_sub (rename_subst f s) /].
    Proof.
      induction e;
        basic_goal_prep;
        basic_term_crush.
      {
        unfold parameterize_sub.
        apply parameterize_subst_lookup; auto.
        firstorder.
      }
      {
        rewrite !map_app, !map_map;
          simpl.
        f_equal.
        {
          revert H.
          induction l;
            basic_goal_prep;
            basic_term_crush.
        }
        {
          f_equal.
          rewrite subst_lookup_p_name; auto.
          apply p_name_fresh_in_subst.
        }
      }
    Qed.
    
    Lemma parameterize_args_subst e s
      : parameterize_args (map (rename f) e) [/rename_subst f s /]
        = (parameterize_args (map (rename f) e)) [/parameterize_sub (rename_subst f s) /].
    Proof.
      induction e;
        basic_goal_prep;
        basic_term_crush.
      {
        cbn; f_equal.
        rewrite subst_lookup_p_name; auto.
        apply p_name_fresh_in_subst.
      }
      {
        cbn.
        unfold parameterize_args in *.
        fold_Substable.
        f_equal; auto.
        rewrite !parameterize_term_subst; eauto.
      }
    Qed.

    Lemma parameterize_sort_subst e s
      : parameterize_sort (rename_sort f e) [/rename_subst f s /]
        = (parameterize_sort (rename_sort f e)) [/parameterize_sub (rename_subst f s) /].
    Proof.
      destruct e;
        basic_goal_prep.
      pose proof parameterize_args_subst as H';
        unfold parameterize_args in H';
        rewrite H'; eauto.
    Qed.

    (*TODO: move to Rule.v*)
    Definition get_ctx (r : rule) :=
      match r with
      | sort_rule c _
      | term_rule c _ _
      | sort_eq_rule c _ _
      | term_eq_rule c _ _ _ => c
      end.

    Lemma parameterization_monotonicity
      l lp (l':= (parameterize_lang (rename_lang f l))++lp)
      : all_fresh l' ->
        (forall c t1 t2,
            eq_sort l c t1 t2 ->
            eq_sort l' (parameterize_ctx (rename_ctx f c))
              (parameterize_sort (rename_sort f t1))
              (parameterize_sort (rename_sort f t2)))
        /\ (forall c t e1 e2,
               eq_term l c t e1 e2 ->
               eq_term l' (parameterize_ctx (rename_ctx f c))
                 (parameterize_sort (rename_sort f t))
                 (parameterize_term (rename f e1))
                 (parameterize_term (rename f e2)))
        /\ (forall c c' s1 s2,
               eq_subst l c c' s1 s2 ->
               eq_subst l' (parameterize_ctx (rename_ctx f c))
                 (parameterize_ctx (rename_ctx f c'))
                 (parameterize_sub (rename_subst f s1))
                 (parameterize_sub (rename_subst f s2)))
        /\ (forall c t,
               wf_sort l c t ->
               wf_sort l' (parameterize_ctx (rename_ctx f c))
                 (parameterize_sort (rename_sort f t)))
        /\ (forall c e t,
               wf_term l c e t ->
               wf_term l' (parameterize_ctx (rename_ctx f c))
                 (parameterize_term (rename f e))
                 (parameterize_sort (rename_sort f t)))
        /\ (forall c s c',
               wf_args l c s c' ->
               wf_args l' (parameterize_ctx (rename_ctx f c))
                 (parameterize_args (map (rename f) s))
                 (parameterize_ctx (rename_ctx f c)))
        /\ (forall c,
               wf_ctx l c ->
               wf_ctx l' (parameterize_ctx (rename_ctx f c))).
Proof using.
  intros all_fresh.
  apply judge_ind; basic_goal_prep.
  all: try solve [constructor; eauto].
  all: erewrite ?rename_sort_distr_subst, ?rename_distr_subst by assumption.
  all: rewrite ?parameterize_term_subst, ?parameterize_sort_subst.
  {
    subst l'.
    eapply eq_sort_by.
    eapply in_or_app; left.
    unfold parameterize_lang, rename_lang.
    rewrite map_map; simpl.
    eapply in_map in H; exact H.
  }
  1:basic_core_crush.
  1:basic_core_crush.
  1:solve [basic_core_crush].
  
  {
    subst l'.
    eapply eq_term_by.
    eapply in_or_app; left.
    unfold parameterize_lang, rename_lang.
    rewrite map_map; simpl.
    eapply in_map in H; exact H.
  }  
  1:solve [basic_core_crush].
  1:solve [basic_core_crush].
  {
    cbn.
    repeat constructor.
    unfold parameterize_ctx.
    basic_utils_crush.
    right.
    simpl.
    left.
    f_equal.
    admit (*TODO: find lemma*).
  }
  {
    cbn.
    constructor; basic_core_crush.
    TODO: need hypothesis to be in terms of V = V - p_name
  1:solve [basic_core_crush].
  1:solve [basic_core_crush].
  1:solve [basic_core_crush].
  1:solve [basic_core_crush].
  1:solve [basic_core_crush].
  1:solve [basic_core_crush].
  {
    basic_core_crush.
    TODO: why are s1, s2 not renamed?
    rewrite <- !rename_sort_distr_subst.
     all: rewrite <- ?parameterize_term_subst, <- ?parameterize_sort_subst.
 
    Idea: rename via V -> V' renaming, using a subset type

    all: rewrite ?parameterize_term_subst, ?parameterize_sort_subst.
    TODO: how to rename? generalize mutual inductive to include list of reserved names?
      - relies on V being infinite
    eapply eq_sort_subst; cycle 1; eauto. }
  {
    TODO: what to do about ctxs in eq_sort_subst? alpha-rename? cut elim?
    alpha:                                                          
    pair of lemmas for renaming a ctx
  }
  constructor. eauto].
    eauto.
    rewrite parameterize_sort_subst; eauto.
      TODO: commute w/ subst
Qed.
    
    End WithParameter.

End WithVar.

Require Import Pyrosome.Lang.SimpleVSubst.

Compute (parameterize_lang "D" {{s #"ty_env"}}
           value_subst
        ).
