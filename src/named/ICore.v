Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From Utils Require Import Utils.
From Named Require IExp IRule Rule.
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
    elab_subst l c (zip args s) (with_names_from c' es) c' ->
    elab_sort l c (IExp.srt n s) (Exp.srt n es)
with elab_term l c : IExp.exp -> exp -> sort -> Prop :=
| elab_term_by : forall n s es c' t args,
    (n, (term_rule c' args t)) \in l ->
    elab_subst l c (zip args s) (with_names_from c' es) c' ->
    elab_term l c (IExp.con n s) (con n es) t[/(with_names_from c' es)/]
(* terms can be lifted to greater (less precise) types,
   but not the other way around; TODO: change the direction? might be more intuitive
 *)
| elab_term_conv : forall e ee t t',
    (* We add this condition so that we satisfy the assumptions of le_sort *)
    wf_sort (strip_args l) c t' ->  
    elab_term l c e ee t ->
    le_sort (strip_args l) c t t' ->
    elab_term l c e ee t'
| elab_term_var : forall n t,
    (n, t) \in c ->
    elab_term l c (IExp.var n) (var n) t
| elab_term_ann : forall e ee t et,
    elab_sort l c t et ->
    elab_term l c e ee et ->
    elab_term l c (IExp.ann e t) ee et
with elab_subst l c : IExp.subst -> subst -> ctx -> Prop :=
| elab_subst_nil : elab_subst l c [::] [::] [::]
| elab_subst_cons_ex : forall s es c' name e ee t,
    fresh name c' ->
    elab_subst l c s es c' ->
    wf_sort (strip_args l) c' t ->
    elab_term l c e ee t[/es/] ->
    elab_subst l c ((name,e)::s) ((name,ee)::es) ((name,t)::c')
| elab_subst_cons_im : forall s es c' name e ee t,
    fresh name c' ->
    elab_subst l c s es c' ->
    wf_sort (strip_args l) c' t ->
    elab_term l c e ee t[/es/] ->
    elab_subst l c s ((name,ee)::es) ((name,t)::c').

Inductive elab_ctx l : IExp.ctx -> ctx -> Prop :=
| elab_ctx_nil : elab_ctx l [::] [::]
| elab_ctx_cons : forall name c ec v ev,
    fresh name c ->
    elab_ctx l c ec ->
    elab_sort l ec v ev ->
    elab_ctx l ((name,v)::c) ((name,ev)::ec).

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

Inductive elab_lang : IRule.lang -> lang -> Prop :=
| elab_lang_nil : elab_lang [::] [::]
| elab_lang_cons : forall l el name r er,
    fresh name l ->
    elab_lang l el ->
    elab_rule el r er ->
    elab_lang ((name,r)::l) ((name,er)::el).

Lemma elab_lang_wf l el : elab_lang l el -> wf_lang (strip_args el).
Admitted.


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
    elab_subst l c (zip args s) (Core.with_names_from c' es) c' ->
    elab_sort l c (IExp.srt n s) (Exp.srt n es).
Proof using .
  intros.
  econstructor; eassumption.
Qed. 

Lemma elab_term_by' l c : forall n s es t,
    let r := named_list_lookup (ARule.sort_rule [::] [::]) l n in
    let c' := get_rule_ctx r in
    let args := get_rule_args r in
    let t' := get_rule_sort r in
    (n, (term_rule c' args t')) \in l ->
    elab_subst l c (zip args s) (with_names_from c' es) c' ->
    t = t'[/(with_names_from c' es)/] ->
    elab_term l c (IExp.con n s) (con n es) t.
Proof.
  intros.
  rewrite H1.
  eapply elab_term_by; eassumption.
Qed.  
