Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
Import Core.Notations.


Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
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

Section TermsAndRules.
  Context (l : lang).

  (*All assume wf_lang.
    All ctxs (other than in wf_ctx) are assumed to satisfy wf_ctx.
    Judgments whose assumptions take ctxs must ensure they are wf.
    Sorts are not assumed to be wf; the term judgments should guarantee
    that their sorts are wf.
   *)
  
 Inductive elab_term : ctx -> term -> term -> sort -> Prop :=
  | elab_term_by : forall c n s es args c' t,
      In (n, term_rule c' args t) l ->
      elab_args c s args es c' ->
      elab_term c (con n s) (con n es) t[/(with_names_from c' es)/]
  | elab_term_conv : forall c e ee t t',
      elab_term c e  ee t ->
      eq_sort l c t t' ->
      elab_term c e ee t'
  | elab_term_var : forall c n t,
      In (n, t) c ->
      elab_term c (var n) (var n) t
  with elab_args : ctx -> list term -> list V -> list term -> ctx -> Prop :=
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
      wf_term l c ee t[/with_names_from c' es/] ->
      elab_args c s args (ee::es) ((name,t)::c')
  with elab_sort : ctx -> sort -> sort -> Prop :=
  | elab_sort_by : forall c n s args es c',
      In (n, (sort_rule c' args)) l ->
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

 Lemma elab_ctx_preserves_fresh c ec n
   : elab_ctx c ec ->
     fresh n c ->
     fresh n ec.
 Proof.
   induction 1; basic_goal_prep; basic_core_firstorder_crush.
 Qed.
 Hint Resolve elab_ctx_preserves_fresh : lang_core.
 
 Local Lemma elab_implies_wf
   : (forall c t et,
         elab_sort c t et ->
         wf_sort l c et)
     /\ (forall c e ee t,
            elab_term c e ee t ->
            wf_term l c ee t)
     /\ (forall c s args es c',
            elab_args c s args es c' ->
            wf_args l c es c')
     /\ (forall c ec,
            elab_ctx c ec ->
            wf_ctx l ec).
 Proof using.
   apply elab_ind; basic_goal_prep; basic_core_crush.
 Qed.

 Definition elab_sort_implies_wf := proj1 elab_implies_wf.
 Hint Resolve elab_sort_implies_wf : lang_core.

 Definition elab_term_implies_wf := proj1 (proj2 elab_implies_wf).
 Hint Resolve elab_term_implies_wf : lang_core.

 Definition elab_args_implies_wf := proj1 (proj2 (proj2 elab_implies_wf)).
 Hint Resolve elab_args_implies_wf : lang_core.

 Definition elab_ctx_implies_wf := proj2 (proj2 (proj2 elab_implies_wf)).
 Hint Resolve elab_ctx_implies_wf : lang_core.


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
 
 Lemma elab_rule_implies_wf r er
   : elab_rule r er ->
     wf_rule l er.
 Proof using.
   destruct 1; basic_goal_prep; basic_core_crush.
 Qed.

(* TODO: do I need this?
  Inductive elab_subst c : subst -> ctx -> Prop :=
  | elab_subst_nil : elab_subst c [] []
  | elab_subst_cons : forall s c' name e t,
      (* assumed because the output ctx is wf: fresh name c' ->*)
      elab_subst c s c' ->
      elab_term c e t[/s/] ->
      elab_subst c ((name,e)::s) ((name,t)::c').
 *)
 
End TermsAndRules.

Section Extension.
  Context (l_pre : lang).
  
  Inductive elab_lang_ext : lang -> lang -> Prop :=
  | elab_lang_nil : elab_lang_ext [] []
  | elab_lang_cons : forall l el n r er,
      fresh n (el ++ l_pre) ->
      elab_lang_ext l el ->
      elab_rule (el++l_pre) r er ->
      elab_lang_ext ((n,r)::l) ((n,er)::el).
  Hint Constructors elab_lang_ext : lang_core.

  Lemma elab_lang_preserves_fresh l el n
    : elab_lang_ext l el ->
      fresh n l ->
      fresh n el.
  Proof.
    induction 1; basic_goal_prep; basic_core_crush.
  Qed.
  Local Hint Resolve elab_lang_preserves_fresh : lang_core.
  
  Local Hint Resolve elab_rule_implies_wf : lang_core.
  
  Lemma elab_lang_implies_wf l el
    : elab_lang_ext l el ->
      wf_lang_ext l_pre el.
  Proof using.
    induction 1; basic_goal_prep; basic_core_crush.
  Qed.
  Hint Resolve elab_lang_implies_wf : lang_core.
  
  Lemma elab_lang_cons_nth_tail n l el name r er el'
    : nth_error l n = Some (name,r) ->
      nth_tail n el = (name, er)::el' ->
      fresh name (nth_tail (S n) l ++ l_pre) ->
      elab_lang_ext (nth_tail (S n) l) (nth_tail (S n) el) ->
      wf_lang l_pre ->
      (wf_lang (nth_tail (S n) el++l_pre) ->
       elab_rule (nth_tail (S n) el++ l_pre) r er) ->
      elab_lang_ext (nth_tail n l) (nth_tail n el).
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
        eapply IHl; basic_core_crush.
      }
    }
  Qed.

End Extension.

Hint Resolve elab_lang_preserves_fresh : lang_core.

Hint Constructors elab_sort elab_term elab_args elab_ctx elab_rule elab_lang_ext : lang_core.
(* TODO: are these hints worth it?
#[export] Hint Resolve elab_sort_implies_wf : lang_core.
#[export] Hint Resolve elab_term_implies_wf : lang_core.
#[export] Hint Resolve elab_args_implies_wf : lang_core.
#[export] Hint Resolve elab_ctx_implies_wf : lang_core.
  Hint Resolve elab_rule_implies_wf : lang_core.
*)
Hint Resolve elab_lang_implies_wf : lang_core.

(*TODO: improve connection between elab, prefix elab, and wf
  so that wf theorems can be ported to the others.
  Avoids duplication
*)
Local Lemma elab_lang_mono l' l
  : incl l l' ->
    (forall c t et,
           elab_sort l c t et ->
           elab_sort l' c t et)
    /\ (forall c e ee t,
           elab_term l c e ee t ->
           elab_term l' c e ee t)
    /\ (forall c s args es c',
           elab_args l c s args es c' ->
           elab_args l' c s args es c')
    /\ (forall c ec,
           elab_ctx l c ec ->
           elab_ctx l' c ec).
Proof using.
  intros.
  apply elab_ind; basic_goal_prep; basic_core_crush.
  {
    eapply elab_term_conv; basic_core_crush.
    (*TODO: add to db?*)
    eauto using eq_sort_lang_monotonicity.
  }
  {
    constructor; basic_core_crush.
    (*TODO: add to db?*)
    eauto using wf_term_lang_monotonicity.
  }
Qed.


Definition elab_sort_lang_monotonicity l' l (lincll' : incl l l')
  := proj1 (elab_lang_mono lincll').
Hint Resolve elab_sort_lang_monotonicity : lang_core.

Definition elab_term_lang_monotonicity l' l (lincll' : incl l l')
  := proj1 (proj2 (elab_lang_mono lincll')).
Hint Resolve elab_term_lang_monotonicity : lang_core.

Definition elab_args_lang_monotonicity l' l (lincll' : incl l l')
  := proj1 (proj2 (proj2 (elab_lang_mono lincll'))).
Hint Resolve elab_args_lang_monotonicity : lang_core.

Definition elab_ctx_lang_monotonicity l' l (lincll' : incl l l')
  := proj2 (proj2 (proj2 (elab_lang_mono lincll'))).
Hint Resolve elab_ctx_lang_monotonicity : lang_core.



Lemma elab_term_by' l c n (s es : list term) args c' t t'
  : In (n, term_rule c' args t') l ->
    elab_args l c s args es c' ->
    t = t' [/with_names_from c' es /] \/ eq_sort l c t' [/with_names_from c' es /] t ->
    elab_term l c (con n s) (con n es) t.
Proof.
  intros; subst; intuition subst; eauto with lang_core.
Qed.

Lemma wf_term_by' l c n (es : list term) args c' t t'
  : In (n, term_rule c' args t') l ->
    wf_args l c es c' ->
    t = t' [/with_names_from c' es /] \/ eq_sort l c t' [/with_names_from c' es /] t ->
    wf_term l c (con n es) t.
Proof.
  intros; subst; intuition subst; eauto with lang_core.
Qed.


Lemma elab_args_cons_ex' l c s args es c' name e ee t
  : len_eq es c' -> (*used to instantiate es with conses*)
    elab_term l c e ee t[/with_names_from c' es/] ->
    (* these arguments are last so that proof search unifies existentials
       from the other arguments first*)
    elab_args l c s args es c' ->
    elab_args l c (e::s) (name::args) (ee::es) ((name,t)::c').
Proof.
  eauto with lang_core.
Qed.


Definition annotation (x : V) (e : term) : option term := None.
Definition ann_cons an l : list term :=
  match an with
  | Some e => e::l
  | None => l
  end.

Lemma elab_args_cons_im_ann : forall (l : lang) c s args es c' name e ee t,
    len_eq es c' ->
    elab_term l c e ee t[/with_names_from c' es/] ->
    elab_args l c s args es c' ->
    elab_args l c (ann_cons (annotation name e) s) args (ee::es) ((name,t)::c').
Proof.
  intros.
  cbv [ann_cons annotation].
  eapply elab_args_cons_im; eauto using elab_term_implies_wf.
Qed.

End WithVar.

#[export] Hint Resolve elab_ctx_preserves_fresh : lang_core.
#[export] Hint Resolve elab_sort_implies_wf : lang_core.
#[export] Hint Resolve elab_term_implies_wf : lang_core.
#[export] Hint Resolve elab_args_implies_wf : lang_core.
#[export] Hint Resolve elab_ctx_implies_wf : lang_core.
#[export] Hint Resolve elab_rule_implies_wf : lang_core.
#[export] Hint Resolve elab_lang_implies_wf : lang_core.
#[export] Hint Resolve elab_lang_preserves_fresh : lang_core.
#[export] Hint Constructors elab_sort elab_term elab_args elab_ctx elab_rule elab_lang_ext : lang_core.
#[export] Hint Resolve elab_sort_lang_monotonicity : lang_core.
#[export] Hint Resolve elab_term_lang_monotonicity : lang_core.
#[export] Hint Resolve elab_args_lang_monotonicity : lang_core.
#[export] Hint Resolve elab_ctx_lang_monotonicity : lang_core.

(* TODO: refactor/move/delete all of these tactics *)


Ltac break_down_elab_lang :=
  repeat ((eapply elab_lang_cons_nth_tail; [vm_compute; reflexivity | vm_compute; reflexivity| apply use_compute_fresh; compute; reflexivity | ..]));
  [solve [assumption | compute; apply elab_lang_nil]|..].


Ltac solve_fresh := eapply use_compute_fresh; vm_compute; reflexivity.
Ltac solve_sublist := eapply use_sublistb;
                      try typeclasses eauto;
                      vm_compute; reflexivity.


Ltac break_eq_args :=
  (apply eq_args_cons;[break_eq_args|])
  || apply eq_args_nil.



Ltac solve_in := apply named_list_lookup_err_in; vm_compute; reflexivity.
Ltac solve_len_eq := solve[ repeat constructor].

(*TODO: move to the right place*)
Ltac compute_everywhere e :=
  let e' := eval vm_compute in e in
      change e with e' in *.

Declare Custom Entry ann_arg.
Declare Custom Entry ann_arg_list.

Notation "a" := (Some a) (in custom ann_arg at level 40, a custom arg).
Notation "@( x ':=' e )" :=
  (annotation x e)
    (in custom ann_arg at level 0,
        e custom term at level 99,
        x constr at level 0,
        format "'[hv' @( x  :=  e ) ']'").


  Notation "@ c al" :=
    (con c%string al)
      (right associativity,
        in custom term at level 60,
           c constr at level 0,
           al custom ann_arg_list,
           format "'[' @ c al ']'").
  
  Notation "@ c al" :=
    (scon c%string al)
      (right associativity,
        in custom sort at level 60,
           c constr at level 0,
           al custom ann_arg_list,
           format "'[' @ c al ']'").

Notation "a1 .. an" :=
  (ann_cons an .. (ann_cons a1 nil) ..)
    (right associativity,
      in custom ann_arg_list at level 50,
        a1 custom ann_arg, an custom ann_arg,
        format " '[hv' a1  ..  an ']'").


Goal False.
  pose {{e @"foo" "bar" #"baz" @("x" := #"5") #"qux" }}.
  pose {{e @"hd" @("A" := "A") }}.
  pose {{e @"foo" "bar" #"baz" @("y" := #"f" "x") @("x" := #"5") #"qux" }}.
Abort.

Ltac cbn_elab_goal :=
  lazymatch goal with
  | |- elab_term ?l ?ctx ?e ?ee ?t =>
      let ctx' := eval cbn - [ann_cons annotation] in ctx in
        let e' := eval cbn - [ann_cons annotation] in e in
          let ee' := eval cbn - [ann_cons annotation] in ee in
            let t' := eval cbn - [ann_cons annotation] in t in
              change_no_check (elab_term l ctx' e' ee' t')
  end.

