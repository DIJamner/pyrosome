Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import List String.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Exp ARule.
(*TODO: why does this generate warnings?*)
Import Exp.Notations.
Import ARule.Notations.
  
Section TermsAndRules.
  Context (l' : lang).

  (* Assumes that the inputs are well-formed in the appropriate settings*)
  Inductive elab_term : exp -> exp -> Prop :=
  | elab_var x : elab_term (var x) (var x)
  | elab_con n s s' c' args t
    : In (n, (term_rule c' args t)) l' ->
      elab_args args s (map fst c') s' ->
      elab_term (con n s) (con n s')
  with elab_args : list string -> list exp -> list string -> list exp -> Prop :=
  | elab_args_nil : elab_args [] [] [] []
  | elab_args_cons_ex e e' s s' n args args'
    : elab_term e e' ->
      elab_args args s args' s' ->
      elab_args (n::args) (e::s) (n::args') (e'::s')
  | elab_args_cons_im e e' s s' n args args'
    : elab_term e e' ->
      elab_args args s args' s' ->
      elab_args args s (n::args') (e'::s').

  Inductive elab_sort : sort -> sort -> Prop :=
  | elab_scon n s s' c' args
    : In (n, (sort_rule c' args)) l' ->
      elab_args args s (map fst c') s' ->
      elab_sort (scon n s) (scon n s').
  
  Definition elab_subst : subst -> subst -> Prop :=
    List.Forall2 (fun '(n,t) '(n',t') => n = n' /\ elab_term t t').

  Definition elab_ctx : ctx -> ctx -> Prop :=
    List.Forall2 (fun '(n,t) '(n',t') => n = n' /\ elab_sort t t').

  Variant elab_rule : rule -> rule -> Prop :=
  | elab_sort_rule : forall c c' args,
      elab_ctx c c' ->
      elab_rule (sort_rule c args) (sort_rule c' args)
  | elab_term_rule : forall c c' args t t',
      elab_ctx c c' ->
      elab_sort t t' ->
      elab_rule (term_rule c args t) (term_rule c' args t')
  | elab_le_sort_rule : forall c c' t1 t2 t1' t2',
      elab_ctx c c' ->
      elab_sort t1 t1' ->
      elab_sort t2 t2' ->
      elab_rule (sort_le c t1 t2) (sort_le c' t1' t2')
  | elab_le_term_rule : forall c c' e1 e1' e2 e2' t t',
      elab_ctx c c' ->
      elab_sort t t' ->
      elab_term e1 e1' ->
      elab_term e2 e2' ->
      elab_rule (term_le c e1 e2 t) (term_le c' e1' e2' t').
End TermsAndRules.
  
Inductive elab_lang : lang -> lang -> Prop :=
| elab_lang_nil : elab_lang [] []
| elab_lang_cons n l l' r r'
  : elab_lang l l' ->
    elab_rule l' r r' ->
    elab_lang ((n,r)::l) ((n,r')::l').

Hint Constructors elab_lang elab_rule elab_sort List.Forall2 elab_args elab_term : exp.
