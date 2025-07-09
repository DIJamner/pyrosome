Require Import Lists.List.
Import ListNotations.
Open Scope list.
From Utils Require Import Utils SymmetricInduction.
From Pyrosome.Theory Require Import Core (*CutElim*) .


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

  
  Local Notation wf_subst l c s c' := (wf_subst (Model:=core_model l) c s c').
  
  Section Terms.
  Context (l : lang).

  Section WithCtx.
    Context (c : ctx).

    (*TODO: move this to the definition*)
    Arguments eq_sort {V}%type_scope {V_Eqb} l c _ _.

    Inductive wf_term : term -> sort -> Prop :=
    | wf_term_cong : forall name c' args t s,
        In (name,term_rule c' args t) l ->
        wf_args s c' ->
        wf_term (con name s) t[/(with_names_from c' s)/]
    | wf_term_var : forall n t,
        In (n, t) c ->
        wf_term (var n) t
    (* TODO: separate conv case or no? *)
    | wf_term_conv : forall e t t',
        wf_term e t ->
        eq_sort l c t t' ->
        wf_term e t'
    with wf_args : list term -> ctx -> Prop :=
    | wf_args_nil : wf_args [] []
    | wf_args_cons : forall (c' : ctx) (es : list term),
        wf_args es c' ->
        forall (name : V) (t : sort) (e : term),
          wf_term e t [/with_names_from c' es /] ->
          wf_args (e :: es) ((name, t) :: c').


    Variant wf_sort : sort -> Prop :=
      | wf_sort_cong : forall name c' args s,
          In (name,sort_rule c' args) l ->
          wf_args s c' ->
          wf_sort (scon name s).    

    Scheme wf_term_ind' := Minimality for wf_term Sort Prop
        with wf_args_ind' := Minimality for wf_args Sort Prop.
    
    Combined Scheme wf_cut_ind' from wf_term_ind', wf_args_ind'.
    
    Local Hint Constructors wf_sort wf_term wf_args : lang_core.

  End WithCtx.

  Local Lemma core_implies_cut_wf
    : (forall c t,
             Core.wf_sort l c t ->
             wf_sort c t)
      /\ (forall c e t,
             Core.wf_term l c e t ->
             wf_term c e t)
      /\ (forall c s c',
             Model.wf_args (Model:=core_model l) c s c' ->
             wf_args c s c').
  Proof using.
    apply wf_judge_ind;
      basic_goal_prep.
    all:try econstructor; eauto.
  Qed.

  Context (c:ctx).
  
  Local Lemma cut_implies_core_wf
    : (forall e t,
          wf_term c e t -> Core.wf_term l c e t)
      /\ (forall s c',
             wf_args c s c' -> Model.wf_args (Model:=core_model l) c s c').
  Proof.
    eapply wf_cut_ind';
      basic_goal_prep;
      basic_core_crush.
  Qed.

  Lemma cut_wf_term_iff_core_wf e t : wf_term c e t <-> Core.wf_term l c e t.
  Proof. split; [ apply cut_implies_core_wf | apply core_implies_cut_wf]. Qed.
  Local Hint Rewrite cut_wf_term_iff_core_wf : lang_core.
  
  Lemma cut_wf_args_iff_core_wf s c' : wf_args c s c' <-> Model.wf_args (Model:=core_model l) c s c'.
  Proof. split; [ apply cut_implies_core_wf | apply core_implies_cut_wf]. Qed.
  Local Hint Rewrite cut_wf_args_iff_core_wf : lang_core.

  Section WfCutInd.
    
    Context (P : term -> sort -> Prop)
      (P0 : list term -> named_list sort -> Prop)
      (H1 : forall (name : V) (c' : named_list sort) (args : list V) (t : sort) (s : list term),
          In (name, term_rule c' args t) l ->
          Model.wf_args (Model:=core_model l) c s c' ->
          P0 s c' ->
          P (con name s) t [/with_names_from c' s /])
      (H2 : forall (n : V) (t : sort), In (n, t) c -> P (var n) t)
      (H3 : forall (e : term) (t t' : sort),
          Core.wf_term l c e t -> P e t -> eq_sort l c t t' -> P e t')
      (H4 : P0 [] [])
      (H5 : forall (c' : named_list sort) (es : list term),
          Model.wf_args (Model:=core_model l) c es c' ->
          P0 es c' ->
          forall (name : V) (t : sort) (e : term),
            Core.wf_term l c e t [/with_names_from c' es /] ->
            P e t [/with_names_from c' es /] -> P0 (e :: es) ((name, t) :: c')).

    Theorem wf_cut_ind
      : (forall (t : term) (s : sort), Core.wf_term l c t s -> P t s) /\
          (forall s c', Model.wf_args (Model:=core_model l) c s c' -> P0 s c').
    Proof.
      enough ((forall (t : term) (s : sort), wf_term c t s -> P t s) /\
                (forall (s : list term) (c0 : named_list sort), wf_args c s c0 -> P0 s c0)) as H.
      {
        revert H; clear.
        intuition subst.
        { apply H0; autorewrite with lang_core in *; eauto. }
        {
          apply H1.
          eapply core_implies_cut_wf; eauto.
        }
      }
      {
        pose proof core_implies_cut_wf.
        apply wf_cut_ind'.
        all: intuition (autorewrite with lang_core in *; eauto).
      }
    Qed.

  End WfCutInd.
  
  Section TermCutInd.
    
    Context (P : term -> sort -> Prop).

    
    Fixpoint P_args s c' :=
      match c', s with
      | [], [] => True
      | (n,t)::c', e::s =>
          P_args s c'
          /\ P e t[/with_names_from c' s/]
      | _, _ => False
      end.

    Context
      (H1 : forall (name : V) (c' : named_list sort) (args : list V) (t : sort) (s : list term),
          In (name, term_rule c' args t) l ->
          Model.wf_args (Model:=core_model l) c s c' ->
          P_args s c' ->
          P (con name s) t [/with_names_from c' s /])
        (H2 : forall (n : V) (t : sort), In (n, t) c -> P (var n) t)
        (H3 : forall (e : term) (t t' : sort),
            Core.wf_term l c e t -> P e t -> eq_sort l c t t' -> P e t').

    Theorem wf_term_cut_ind
      : forall (t : term) (s : sort), Core.wf_term l c t s -> P t s.
    Proof.
      enough ((forall (t : term) (s : sort), Core.wf_term l c t s -> P t s) /\
                (forall s c', Model.wf_args (Model:=core_model l) c s c' -> P_args s c'))
        by intuition.
      apply wf_cut_ind;
        intuition eauto.
      all: cbn;
        intuition eauto.
    Qed.

  End TermCutInd.

  End Terms.

  Lemma invert_wf_term_con l c n s (t : sort)
    : Core.wf_term l c (con n s) t ->
      exists c' args t', In (n, term_rule c' args t') l
                         /\ Model.wf_args (Model:=core_model l) c s c'
                         /\ (eq_sort l c t'[/with_names_from c' s/] t
                             \/ t'[/with_names_from c' s/] = t).
  Proof.
    intro H.
    remember (con n s) as e.
    revert n s Heqe.
    pattern t.
    pattern e.
    revert e t H.
    apply wf_term_cut_ind;
      intros; subst; inversions; try tauto.
    {
      repeat eexists; intuition eauto.
    }
    {
      specialize (H0 _ _ eq_refl).
      break.
      repeat eexists; intuition eauto.
      { left; eapply eq_sort_trans; eauto. }
      { subst; left; eauto. }
    }
  Qed.

End WithVar.
