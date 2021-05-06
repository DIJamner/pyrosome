Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Elab.
Import Core.Notations.

(*TODO: move to elab*)
Lemma elab_lang_preserves_fresh' c ec n
  : elab_lang c ec ->
    fresh n ec ->
    fresh n c.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
Qed.
#[export] Hint Resolve elab_lang_preserves_fresh' : lang_core.

Section WithPrefix.
  Context (l_pre : lang) (*assumed to already be elaborated*).

  Section TermsAndRules.
    Context (l : lang).

    (*All assume wf_lang.
    All ctxs (other than in wf_ctx) are assumed to satisfy wf_ctx.
    Judgments whose assumptions take ctxs must ensure they are wf.
    Sorts are not assumed to be wf; the term judgments should guarantee
    that their sorts are wf.
     *)
    
    Inductive elab_term : ctx -> exp -> exp -> sort -> Prop :=
    | elab_term_by : forall c n s es args c' t,
        In (n, term_rule c' args t) (l ++ l_pre) ->
        elab_args c s args es c' ->
        elab_term c (con n s) (con n es) t[/(with_names_from c' es)/]
    | elab_term_conv : forall c e ee t t',
        elab_term c e  ee t ->
        eq_sort (l ++ l_pre) c t t' ->
        elab_term c e ee t'
    | elab_term_var : forall c n t,
        In (n, t) c ->
        elab_term c (var n) (var n) t
    with elab_args : ctx -> list exp -> list string -> list exp -> ctx -> Prop :=
    | elab_args_nil : forall c, elab_args c [] [] [] []
    | elab_args_cons_ex : forall c s args es c' name e ee t,
        elab_term c e ee t[/with_names_from c' es/] ->
        (* these arguments are last so that proof search unifies existentials
       from the other arguments first*)
        elab_args c s args es c' ->
        elab_args c (e::s) (name::args) (ee::es) ((name,t)::c')
    | elab_args_cons_im : forall c s args es c' name ee t,
        elab_args c s args es c' ->
        (* these arguments are last so that proof search unifies existentials
       from the other arguments first*)
        wf_term (l ++ l_pre) c ee t[/with_names_from c' es/] ->
        elab_args c s args (ee::es) ((name,t)::c')
    with elab_sort : ctx -> sort -> sort -> Prop :=
    | elab_sort_by : forall c n s args es c',
        In (n, (sort_rule c' args)) (l ++ l_pre) ->
        elab_args c s args es c' ->
        elab_sort c (scon n s) (scon n es)
    with elab_ctx : ctx -> ctx-> Prop :=
    | elab_ctx_nil : elab_ctx [] []
    | elab_ctx_cons : forall name c ec v ev,
        fresh name c ->
        elab_ctx c ec ->
        elab_sort ec v ev ->
        elab_ctx ((name,v)::c) ((name,ev)::ec).
    
    Hint Constructors elab_sort elab_term elab_args elab_ctx : lang_core.
    
    Scheme elab_sort_ind' := Minimality for elab_sort Sort Prop
      with elab_term_ind' := Minimality for elab_term Sort Prop
      with elab_args_ind' := Minimality for elab_args Sort Prop
      with elab_ctx_ind' := Minimality for elab_ctx Sort Prop.
    Combined Scheme elab_ind
             from  elab_sort_ind', elab_term_ind', elab_args_ind', elab_ctx_ind'.

    Local Lemma elab_prefix_implies_elab
      : (forall c t et,
            elab_sort c t et ->
            Elab.elab_sort (l++l_pre) c t et)
        /\ (forall c e ee t,
               elab_term c e ee t ->
               Elab.elab_term (l++l_pre) c e ee t)
        /\ (forall c s args es c',
               elab_args c s args es c' ->
               Elab.elab_args (l++l_pre) c s args es c')
        /\ (forall c ec,
               elab_ctx c ec ->
               Elab.elab_ctx (l++l_pre) c ec).
    Proof using.
      apply elab_ind; basic_goal_prep; basic_core_crush.
      1,2: eapply Elab.elab_sort_by; basic_core_crush.
      1,2: eapply Elab.elab_term_by; basic_core_crush.
    Qed.

    Definition elab_prefix_implies_elab_sort := proj1 elab_prefix_implies_elab.
    Hint Resolve elab_prefix_implies_elab_sort : lang_core.
    
    Definition elab_prefix_implies_elab_term := proj1 (proj2 elab_prefix_implies_elab).
    Hint Resolve elab_prefix_implies_elab_term : lang_core.

    Definition elab_prefix_implies_elab_args := proj1 (proj2 (proj2 elab_prefix_implies_elab)).
    Hint Resolve elab_prefix_implies_elab_args : lang_core.

    Definition elab_prefix_implies_elab_ctx := (proj2 (proj2 (proj2 elab_prefix_implies_elab))).
    Hint Resolve elab_prefix_implies_elab_ctx : lang_core.

    
    Local Lemma elab_implies_elab_prefix
      : (forall c t et,
            Elab.elab_sort (l++l_pre) c t et ->
            elab_sort c t et)
        /\ (forall c e ee t,
               Elab.elab_term (l++l_pre) c e ee t ->
               elab_term c e ee t)
        /\ (forall c s args es c',
               Elab.elab_args (l++l_pre) c s args es c' ->
               elab_args c s args es c')
        /\ (forall c ec,
               Elab.elab_ctx (l++l_pre) c ec ->
               elab_ctx c ec).
    Proof using.
      apply Elab.elab_ind; basic_goal_prep; basic_core_crush.
      1,2: eapply elab_sort_by; basic_core_crush.
      1,2: eapply elab_term_by; basic_core_crush.
    Qed.

    Definition elab_implies_elab_prefix_sort := proj1 elab_implies_elab_prefix.
    Hint Resolve elab_implies_elab_prefix_sort : lang_core.
    
    Definition elab_implies_elab_prefix_term := proj1 (proj2 elab_implies_elab_prefix).
    Hint Resolve elab_implies_elab_prefix_term : lang_core.

    Definition elab_implies_elab_prefix_args := proj1 (proj2 (proj2 elab_implies_elab_prefix)).
    Hint Resolve elab_implies_elab_prefix_args : lang_core.

    Definition elab_implies_elab_prefix_ctx := (proj2 (proj2 (proj2 elab_implies_elab_prefix))).
    Hint Resolve elab_implies_elab_prefix_ctx : lang_core.

    Variant elab_rule : rule -> rule -> Prop :=
    | elab_sort_rule : forall c ec args,
        elab_ctx c ec ->
        sublist args (map fst ec) ->
        elab_rule (sort_rule c args) (sort_rule ec args)
    | elab_term_rule : forall c ec args t et,
        elab_ctx c ec ->
        elab_sort ec t et ->
        sublist args (map fst ec) ->
        elab_rule (term_rule c args t) (term_rule ec args et)
    | eq_sort_rule : forall c ec t1 et1 t2 et2,
        elab_ctx c ec ->
        elab_sort ec t1 et1 ->
        elab_sort ec t2 et2 ->
        elab_rule (sort_eq_rule c t1 t2) (sort_eq_rule ec et1 et2)
    | eq_term_rule : forall c ec e1 ee1 e2 ee2 t et,
        elab_ctx c ec ->
        elab_sort ec t et ->
        elab_term ec e1 ee1 et ->
        elab_term ec e2 ee2 et ->
        elab_rule (term_eq_rule c e1 e2 t) (term_eq_rule ec ee1 ee2 et).
    Hint Constructors elab_rule : lang_core.

    Lemma elab_prefix_implies_elab_rule r er
      : elab_rule r er ->
        Elab.elab_rule (l++l_pre) r er.
    Proof.
      inversion 1; basic_core_crush.
      constructor; basic_core_crush.
    Qed.

    
    Lemma elab_implies_elab_prefix_rule r er
      : Elab.elab_rule (l++l_pre) r er ->
         elab_rule r er.
    Proof.
      inversion 1; basic_core_crush.
      constructor; basic_core_crush.
    Qed.    
    
  End TermsAndRules.

  
  Hint Resolve elab_implies_elab_prefix_rule : lang_core.
  Hint Resolve elab_prefix_implies_elab_rule : lang_core.

  Inductive elab_lang : lang -> lang -> Prop :=
  | elab_lang_nil : elab_lang [] []
  | elab_lang_cons : forall l el n r er,
      fresh n (l ++ l_pre) ->
      elab_lang l el ->
      elab_rule el r er ->
      elab_lang ((n,r)::l) ((n,er)::el).

  
  Lemma elab_prefix_implies_elab_lang lp l el
    : Elab.elab_lang lp l_pre ->
      elab_lang l el ->
      Elab.elab_lang (l++lp) (el++l_pre).
  Proof.
    induction 2; basic_goal_prep; basic_core_crush.
    constructor; basic_core_crush.
  Qed.

  (*TODO: 2 versions of the same lemma.
    This one should be flipped.
    Since it's not used though, do we need it?

  Lemma elab_implies_elab_prefix_lang lp l el
    : Elab.elab_lang lp l_pre ->
      elab_lang l el ->
      Elab.elab_lang (l++lp) (el++l_pre).
  Proof.
    induction 2; basic_goal_prep; basic_core_crush.
    constructor; basic_core_crush.
  Qed.  
   *)

End WithPrefix.

#[export] Hint Resolve elab_prefix_implies_elab_lang : lang_core.

#[export] Hint Constructors elab_sort elab_term elab_args elab_ctx elab_rule elab_lang : lang_core.

Local Lemma elab_prefix_monotonicity l_pre l_pre' l
  : (forall c t et,
        elab_sort l_pre l c t et ->
        elab_sort (l_pre'++l_pre) l c t et)
    /\ (forall c e ee t,
           elab_term l_pre l c e ee t ->
           elab_term (l_pre'++l_pre) l c e ee t)
    /\ (forall c s args es c',
           elab_args l_pre l c s args es c' ->
           elab_args (l_pre'++l_pre) l c s args es c')
    /\ (forall c ec,
           elab_ctx l_pre l c ec ->
           elab_ctx (l_pre'++l_pre) l c ec).
Proof using.
  apply elab_ind; basic_goal_prep; basic_core_crush.
  1,2: eapply elab_sort_by; basic_core_crush.
  1,2: eapply elab_term_by; basic_core_crush.
Qed.

Definition elab_prefix_monotonicity_sort l_pre l_pre' l
  := proj1 (elab_prefix_monotonicity l_pre l_pre' l).
#[export] Hint Resolve elab_prefix_monotonicity_sort : lang_core.

Definition elab_prefix_monotonicity_term l_pre l_pre' l
  := proj1 (proj2 (elab_prefix_monotonicity l_pre l_pre' l)).
#[export] Hint Resolve elab_prefix_monotonicity_term : lang_core.

Definition elab_prefix_monotonicity_args l_pre l_pre' l
  := proj1 (proj2 (proj2 (elab_prefix_monotonicity l_pre l_pre' l))).
#[export] Hint Resolve elab_prefix_monotonicity_args : lang_core.

Definition elab_prefix_monotonicity_ctx l_pre l_pre' l
  := (proj2 (proj2 (proj2 (elab_prefix_monotonicity l_pre l_pre' l)))).
#[export] Hint Resolve elab_prefix_monotonicity_ctx : lang_core.


Lemma elab_prefix_monotonicity_rule l_pre l_pre' l r er
  : elab_rule l_pre l r er ->
    elab_rule (l_pre'++l_pre) l r er.
Proof.
  inversion 1; basic_core_crush.
  constructor; basic_core_crush.
Qed.
#[export] Hint Resolve elab_prefix_monotonicity_rule : lang_core.


Lemma elab_prefix_monotonicity_lang l_pre l_pre' l el
  : all_fresh (l_pre' ++ l_pre) ->
    all_fresh (l_pre' ++ el) ->
    elab_lang l_pre l el ->
    elab_lang (l_pre' ++ l_pre) l el.
Proof.
  induction 3; basic_goal_prep; basic_core_crush.
  constructor; basic_core_crush.
  eapply all_fresh_insert_is_fresh; eauto.
Qed.
#[export] Hint Resolve elab_prefix_monotonicity_lang : lang_core.


Lemma elab_lang_preserves_fresh l_pre c ec n
  : elab_lang l_pre c ec ->
    fresh n c ->
    fresh n ec.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
Qed.
#[export] Hint Resolve elab_lang_preserves_fresh : lang_core.

Lemma elab_lang_preserves_fresh'' l_pre c ec n
  : elab_lang l_pre c ec ->
    fresh n ec ->
    fresh n c.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
Qed.
#[export] Hint Resolve elab_lang_preserves_fresh'' : lang_core.

(*TODO
Lemma elab_prefix_concat l_pre l el l' el'
  : elab_lang l_pre l el ->
    elab_lang (el++l_pre) l' el' ->
    elab_lang l_pre (l'++l) (el'++el).
Proof.
  induction 2; basic_goal_prep; basic_core_crush.
  constructor; basic_core_crush.
  (*TODO: finish*)
Admitted.
#[export] Hint Resolve elab_prefix_concat : lang_core.
*)


Local Lemma elab_lang_cons_nth_tail' l_pre n l el name r er el'
     : nth_error l n = Some (name, r) ->
       nth_tail n el = (name, er) :: el' ->
       fresh name (nth_tail (S n) l ++ l_pre) ->
       elab_lang l_pre (nth_tail (S n) l) (nth_tail (S n) el) ->
       (elab_lang l_pre (nth_tail (S n) l) (nth_tail (S n) el) ->
        elab_rule l_pre (nth_tail (S n) el) r er) ->
       elab_lang l_pre (nth_tail n l) (nth_tail n el).
  Proof.
  revert el n el'.
  induction l; destruct el; basic_goal_prep; basic_core_crush.
  {
    destruct n.
    {
      rewrite <-!as_nth_tail in *.
      basic_goal_prep;
        basic_core_crush.
      constructor; basic_core_crush.
    }
    {
      rewrite !nth_tail_S_cons in *.
      eapply IHl; eauto.
      basic_core_crush.
    }
  }
Qed.


Lemma elab_lang_cons_nth_tail lp l_pre n l el name r er el'
     : nth_error l n = Some (name, r) ->
       nth_tail n el = (name, er) :: el' ->
       fresh name (nth_tail (S n) l ++ l_pre) ->
       Elab.elab_lang lp l_pre ->
       elab_lang l_pre (nth_tail (S n) l) (nth_tail (S n) el) ->
       (Elab.elab_lang (nth_tail (S n) l ++ lp) (nth_tail (S n) el++l_pre) ->
        Elab.elab_rule (nth_tail (S n) el ++ l_pre) r er) ->
       elab_lang l_pre (nth_tail n l) (nth_tail n el).
Proof.
  intros; eapply elab_lang_cons_nth_tail'; eauto.
  intros.
  apply elab_implies_elab_prefix_rule.
  apply H4.
  apply elab_prefix_implies_elab_lang;
  assumption.
Qed.  
