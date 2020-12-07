Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From Utils Require Import Utils.
From Named Require IExp IRule.
From Named Require Import Rule.
From Named Require Import Core Exp ARule.
Require Import String.

Definition strip_rule_args r :=
  match r with
  | ARule.sort_rule c _ => Rule.sort_rule c
  | ARule.term_rule c _ t => Rule.term_rule c t
  | ARule.sort_le c t1 t2 => Rule.sort_le c t1 t2 
  | ARule.term_le c e1 e2 t => Rule.term_le c e1 e2 t
  end.
    
Definition strip_args : ARule.lang -> Rule.lang :=
  map (fun p=> (fst p, strip_rule_args (snd p))).

(* TODO: are sort annotations worth it? *)
Inductive elab_sort l c : IExp.sort -> sort -> Prop :=
| elab_sort_by : forall n s es c' args,
    (n, (sort_rule c' args)) \in l ->
    elab_args l c s args es c' ->
    elab_sort l c (IExp.srt n s) (Exp.srt n es)
with elab_term l c : IExp.exp -> exp -> sort -> Prop :=
| elab_term_by : forall n s es c' t args,
    (n, (term_rule c' args t)) \in l ->
    elab_args l c s args es c' ->
    elab_term l c (IExp.con n s) (con n es) t[/(with_names_from c' es)/]
(* terms can be lifted to greater (less precise) types,
   but not the other way around; TODO: change the direction? might be more intuitive
 *)
| elab_term_conv : forall e ee t t',
    elab_term l c e ee t ->
    (* We add this condition so that we satisfy the assumptions of le_sort *)
    wf_sort (strip_args l) c t ->  
    le_sort (strip_args l) c t t' ->
    elab_term l c e ee t'
| elab_term_var : forall n t,
    (n, t) \in c ->
    elab_term l c (IExp.var n) (var n) t
| elab_term_ann : forall e ee t et,
    elab_sort l c t et ->
    elab_term l c e ee et ->
    elab_term l c (IExp.ann e t) ee et
with elab_args l c : list IExp.exp -> list string -> list exp -> ctx -> Prop :=
| elab_args_nil : elab_args l c [::] [::] [::] [::]
| elab_args_cons_ex : forall s args es c' name e ee t,
    fresh name c' ->
    elab_term l c e ee t[/with_names_from c' es/] ->
    (* these arguments is last so that proof search unifies existentials
       from the other arguments first*)
    elab_args l c s args es c' ->
    wf_sort (strip_args l) c' t ->
    elab_args l c (e::s) (name::args) (ee::es) ((name,t)::c')
| elab_args_cons_im : forall s args es c' name e ee t,
    fresh name c' ->
    elab_term l c e ee t[/with_names_from c' es/] ->
    (* these arguments is last so that proof search unifies existentials
       from the other arguments first*)
    elab_args l c s args es c' ->
    wf_sort (strip_args l) c' t ->
    elab_args l c s args (ee::es) ((name,t)::c').

Hint Constructors elab_sort elab_term elab_args : judgment.

Inductive elab_subst l c : IExp.subst -> subst -> ctx -> Prop :=
| elab_subst_nil : elab_subst l c [::] [::] [::]
| elab_subst_cons_ex : forall s es c' name e ee t,
    fresh name c' ->
    elab_term l c e ee t[/es/] ->
    (* these arguments is last so that proof search unifies existentials
       from the other arguments first*)
    elab_subst l c s es c' ->
    wf_sort (strip_args l) c' t ->
    elab_subst l c ((name,e)::s) ((name,ee)::es) ((name,t)::c')
| elab_subst_cons_im : forall s es c' name e ee t,
    fresh name c' ->
    elab_term l c e ee t[/es/] ->
    (* these arguments is last so that proof search unifies existentials
       from the other arguments first*)
    elab_subst l c s es c' ->
    wf_sort (strip_args l) c' t ->
    elab_subst l c s ((name,ee)::es) ((name,t)::c').

Hint Constructors elab_subst : judgment.


Inductive elab_ctx l : IExp.ctx -> ctx -> Prop :=
| elab_ctx_nil : elab_ctx l [::] [::]
| elab_ctx_cons : forall name c ec v ev,
    fresh name c ->
    elab_ctx l c ec ->
    elab_sort l ec v ev ->
    elab_ctx l ((name,v)::c) ((name,ev)::ec).

Hint Constructors elab_ctx : judgment.

Fixpoint subseq (s l : list string) : bool :=
  match s,l with
  | [::],_ => true
  | sa::s', [::] => false
  | sa::s', la::l' =>
    if sa == la then subseq s' l'
    else subseq s l'
  end.

Variant elab_rule l : IRule.rule -> rule -> Prop :=
| elab_sort_rule : forall c ec args,
    elab_ctx l c ec ->
    subseq args (map fst ec) ->
    elab_rule l (IRule.sort_rule c args) (sort_rule ec args)
| elab_term_rule : forall c ec args t et,
    elab_ctx l c ec ->
    elab_sort l ec t et ->
    subseq args (map fst ec) ->
    elab_rule l (IRule.term_rule c args t) (term_rule ec args et)
| elab_le_sort_rule : forall c ec t1 et1 t2 et2,
    elab_ctx l c ec ->
    elab_sort l ec t1 et1 ->
    elab_sort l ec t2 et2 ->
    elab_rule l (IRule.sort_le c t1 t2) (sort_le ec et1 et2) 
| elab_le_term_rule : forall c ec e1 ee1 e2 ee2 t et,
    elab_ctx l c ec ->
    elab_sort l ec t et ->
    elab_term l ec e1 ee1 et ->
    elab_term l ec e2 ee2 et ->
    elab_rule l (IRule.term_le c e1 e2 t) (term_le ec ee1 ee2 et).

Hint Constructors elab_rule : judgment.

Inductive elab_lang : IRule.lang -> lang -> Prop :=
| elab_lang_nil : elab_lang [::] [::]
| elab_lang_cons : forall l el name r er,
    fresh name l ->
    elab_lang l el ->
    elab_rule el r er ->
    elab_lang ((name,r)::l) ((name,er)::el).

Hint Constructors elab_lang : judgment.

Lemma elab_lang_cons' : forall l name r er,
    fresh name l ->
    forall el : {el | elab_lang l el},
    elab_rule (proj1_sig el) r er ->
    elab_lang ((name,r)::l) ((name,er)::(proj1_sig el)).
Proof using.
  intros.
  destruct el.
  constructor; assumption.
Qed.

Lemma elab_lang_fresh l el name : elab_lang l el -> fresh name l -> fresh name el.
Proof using .
  elim; auto.
  intros l' el' name' r er.
  unfold fresh.
  intros fn' elab_el' fr_impl elab_r.
  simpl.
  rewrite !in_cons.
  move /norP.
  case => [nneq nnin].
  apply /norP.
  split; tauto.
Qed.

Lemma strip_args_fresh l name : fresh name l -> fresh name (strip_args l).
Proof using .
  elim: l; simpl; auto.
  unfold fresh.
  simpl.
  intros a l IH.
  rewrite !in_cons.
  move /norP => [nneq nnin].
  apply /norP; split; tauto.
Qed.

Lemma elab_ctx_fresh l c ec name
  : elab_ctx l c ec -> fresh name c -> fresh name ec.
Proof using .
  elim; auto.
  intros name' c' ec' t et.
  unfold fresh.
  intros fn' elab_el' fr_impl elab_r.
  simpl.
  rewrite !in_cons.
  move /norP.
  case => [nneq nnin].
  apply /norP.
  split; tauto.
Qed.


Lemma rule_in_strip_args l n r
  : (n,r) \in l -> (n, strip_rule_args r) \in (strip_args l).
Proof using .
  elim: l; auto.
  intros p l IH.
  simpl.
  rewrite !in_cons.
  move /orP; case.
  {
    move /eqP <-.
    apply /orP; left.
    by apply /eqP.
  }
  {
    intro nin.
    apply /orP; right.
    auto.
  }
Qed.


Lemma elab_term_wf l c e ee t
  : elab_term l c e ee t -> wf_term (strip_args l) c ee t
with elab_args_wf l c s args es c'
  : elab_args l c s args es c' -> wf_args (strip_args l) c es c'.
Proof using .
  all: case.
  {
    intros.
    constructor.
    apply rule_in_strip_args in i; exact i.
    eapply elab_args_wf.
    eassumption.
  }
  {
    intros.
    eapply wf_term_conv; try eassumption.
    eapply elab_term_wf; eassumption.
  }
  {
    intros.
    apply wf_term_var; eassumption.
  }
  {
    intros.
    eapply elab_term_wf; eassumption.
  }
  {
    constructor.
  }
  {
    intros.
    constructor; try assumption.
    eapply elab_args_wf; eassumption.
    eapply elab_term_wf; eassumption.
  }
  {
    intros.
    constructor; try assumption.
    eapply elab_args_wf; eassumption.
    eapply elab_term_wf; eassumption.
  }    
Qed.

Hint Resolve elab_term_wf : judgment.
Hint Resolve elab_args_wf : judgment.

Lemma elab_subst_wf l c s es c'
  : elab_subst l c s es c' -> wf_subst (strip_args l) c es c'.
Proof using .
  elim; intros; constructor; eauto with judgment.
Qed.    
Hint Resolve elab_subst_wf : judgment.  

Lemma elab_sort_wf l c t et
  : elab_sort l c t et -> wf_sort (strip_args l) c et.
Proof using .
  elim; econstructor.
  { apply rule_in_strip_args in H; exact H. }
  { eapply elab_args_wf; eassumption. }
Qed.    
Hint Resolve elab_sort_wf : judgment.

Lemma elab_ctx_wf l c ec : elab_ctx l c ec -> wf_ctx (strip_args l) ec.
Proof using .
  elim; constructor.
  { eapply elab_ctx_fresh; eauto. }
  { assumption. }
  { eapply elab_sort_wf; eassumption. }
Qed.
Hint Resolve elab_ctx_wf : judgment.

Lemma elab_rule_wf l r er
  : elab_rule l r er ->
    wf_rule (strip_args l) (strip_rule_args er).
Proof using .
  case; constructor; eauto with judgment.
Qed.
Hint Resolve elab_rule_wf : judgment.

Lemma elab_lang_wf l el : elab_lang l el -> wf_lang (strip_args el).
Proof using .
  elim;simpl; constructor; eauto with judgment.
  {
    apply strip_args_fresh; auto.
    eapply elab_lang_fresh; eauto.
  }
Qed.


Definition get_rule_ctx (r : ARule.rule) : Exp.ctx :=
  match r with
  | ARule.sort_rule c _ => c
  | ARule.term_rule c _ _ => c
  | ARule.sort_le c _ _ => c
  | ARule.term_le c _ _ _ => c
  end.

Definition get_rule_args r :=
  match r with
  | ARule.sort_rule _ args => args
  | ARule.term_rule _ args _ => args
  | ARule.sort_le c _ _ => map fst c
  | ARule.term_le c _ _ _ => map fst c
  end.


Definition get_rule_sort r :=
  match r with
  | ARule.sort_rule _ _ => srt "ERR" [::]
  | ARule.term_rule _ _ t => t
  | ARule.sort_le _ _ _ => srt "ERR" [::]
  | ARule.term_le _ _ _ t => t
  end.

Lemma elab_sort_by' l c : forall n s es,
    let r := named_list_lookup (ARule.sort_rule [::] [::]) l n in
    let c' := get_rule_ctx r in
    let args := get_rule_args r in
    (n, (ARule.sort_rule c' args)) \in l ->
    elab_args l c s args es c' ->
    elab_sort l c (IExp.srt n s) (Exp.srt n es).
Proof using .
  intros.
  econstructor; eassumption.
Qed. 

(* Structured to work well with repeat *)
Lemma elab_term_by' l c : forall n s es t,
    let r := named_list_lookup (ARule.sort_rule [::] [::]) l n in
    let c' := get_rule_ctx r in
    let args := get_rule_args r in
    let t' := get_rule_sort r in
    (n, (term_rule c' args t')) \in l ->
    (*Unnecessary, but helps with evars *)
    len_eq es c' ->
    t = t'[/(with_names_from c' es)/] ->
    (* this argument is last so that proof search unifies existentials
       from the other arguments first*)
    elab_args l c s args es c' ->
    elab_term l c (IExp.con n s) (con n es) t.
Proof using.
  intros.
  rewrite H1.
  eapply elab_term_by; eassumption.
Qed.  

Lemma elab_term_var' n l c t
  : (n, t) \in c ->
    elab_term l c (IExp.var n) (var n) t.
Proof using .
  constructor; assumption.
Qed.
