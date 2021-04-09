Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From Utils Require Import Utils BoolAsProp.
From Named Require Import Exp ARule ImCore Pf PfCore.

Require Import String.
  
Section TermsAndRules.
  Context (l : wfexp_lang)
          (l' : lang).

  (* TODO: Restrict scope of elaboration to just implicit args? *)
  (* Assumes that the inputs are well-formed in the appropriate settings*)
  Inductive elab_term : exp -> wfexp -> Prop :=
  | elab_var x : elab_term (var x) (wf_var x)
  | elab_con n s s' c' args t
    : (n, (Pf.wf_term_rule c' args t)) \in l ->
      elab_args args s (map fst c') s' ->
      elab_term (con n s) (wf_con n s')
  | elab_conv p e e'
    : elab_term e e' ->
      elab_term e (wf_conv p e')
  with elab_args : list string -> list exp -> list string -> list wfexp -> Prop :=
  | elab_args_nil : elab_args [::] [::] [::] [::]
  | elab_args_cons_ex e e' s s' n args args'
    : elab_term e e' ->
      elab_args args s args' s' ->
      n \notin args' ->
      elab_args (n::args) (e::s) (n::args') (e'::s')
  | elab_args_cons_im e e' s s' n args args'
    : elab_term e e' ->
      elab_args args s args' s' ->
      n \notin args' ->
      elab_args args s (n::args') (e'::s').

  Inductive elab_sort : sort -> wfexp -> Prop :=
  | elab_scon n s s' c' args
    : (n, (Pf.wf_sort_rule c' args)) \in l ->
      elab_args args s (map fst c') s' ->
      elab_sort (scon n s) (wf_con n s')
  | elab_sconv p e e'
    : elab_sort e e' ->
      elab_sort e (wf_conv p e').

  
  Definition elab_subst : subst -> subst_wf -> Prop :=
    List.Forall2 (fun '(n,t) '(n',t') => n = n' /\ elab_term t t').

  Definition elab_ctx : ctx -> wfexp_ctx -> Prop :=
    List.Forall2 (fun '(n,t) '(n',t') => n = n' /\ elab_sort t t').

  Variant elab_rule : rule -> wfexp_rule -> Prop :=
  | elab_sort_rule : forall c c' args,
      elab_ctx c c' ->
      subseq args (map fst c) ->
      elab_rule (sort_rule c args) (Pf.wf_sort_rule c' args)
  | elab_term_rule : forall c c' args t t',
      elab_ctx c c' ->
      elab_sort t t' ->
      subseq args (map fst c) ->
      elab_rule (term_rule c args t) (Pf.wf_term_rule c' args t')
  | elab_le_sort_rule : forall c c' t1 t2 t1' t2',
      elab_ctx c c' ->
      elab_sort t1 t1' ->
      elab_sort t2 t2' ->
      elab_rule (sort_le c t1 t2) (wf_sort_le c' t1' t2')
  | elab_le_term_rule : forall c c' e1 e1' e2 e2' t t',
      elab_ctx c c' ->
      elab_sort t t' ->
      elab_term e1 e1' ->
      elab_term e2 e2' ->
      elab_rule (term_le c e1 e2 t) (wf_term_le c' e1' e2' t').
End TermsAndRules.
  
Inductive elab_lang : lang -> wfexp_lang -> Prop :=
| elab_lang_nil : elab_lang [::] [::]
| elab_lang_cons n l l' r r'
  : elab_lang l l' ->
    elab_rule l' r r' ->
    fresh n l' ->
    elab_lang ((n,r)::l) ((n,r')::l').


Hint Constructors elab_lang elab_rule elab_sort List.Forall2 elab_args elab_term : pfcore.

Lemma elab_lang_all_fresh l l'
  : elab_lang l l' -> all_fresh l'.
Proof.
  induction 1; break; simpl in *; pfcore_crush.
  unfold fresh in H1.
  rewrite H2 in H1.
  pfcore_crush.
Qed.
Hint Resolve elab_lang_all_fresh : pfcore.

Lemma elab_ctx_fst_equal l c c'
  : elab_ctx l c c' -> map fst c = map fst c'.
Proof.
  induction 1; break; pfcore_crush.
Qed.

Scheme elab_term_ind' := Minimality for elab_term Sort Prop
  with elab_args_ind' := Minimality for elab_args Sort Prop.
Combined Scheme elab_ta_ind from elab_term_ind', elab_args_ind'.

Lemma elab_args_implicits_subseq l args s args' s'
  : elab_args l args s args' s' ->
    subseq args args'.
Proof.
  induction 1; simpl; pfcore_crush.
  destruct args; pfcore_crush.
Qed.
Hint Resolve  elab_args_implicits_subseq : pfcore.

Lemma elab_ta_deterministic l
  : all_fresh l ->
    (forall e1 e', elab_term l e1 e' ->
                   forall e2, elab_term l e2 e' ->
                              e1 = e2)
    /\ (forall args s1 args' s',
           elab_args l args s1 args' s' ->
           forall s2, elab_args l args s2 args' s' ->
                       s1 = s2).
Proof.
  intro allf.
  apply elab_ta_ind; repeat first [intro; intro_to elab_term | intro; intro_to elab_args].
  all: try solve[inversion 1; try match goal with
             [allf : is_true(all_fresh ?l),
              H1 : is_true((?n,_) \in ?l),
              H2 : is_true((?n,_) \in ?l) |-_]=>
             let H' := fresh in
             pose proof (in_all_fresh_same allf H1 H2) as H';
               inversion H'
           end;subst; repeat f_equal; eauto].
  {
    inversion 1; subst.
    repeat f_equal; eauto.
    pose proof (elab_args_implicits_subseq H12).
    pose proof (subseq_cons_first H5).
    pfcore_crush.
  }
  {
    inversion 1; subst.
    pose proof (elab_args_implicits_subseq H1).
    pose proof (subseq_cons_first H5).
    pfcore_crush.
    repeat f_equal; eauto.
  }
Qed.  

Lemma elab_term_deterministic l e1 e2 e'
  : all_fresh l ->
    elab_term l e1 e' ->
    elab_term l e2 e' ->
    e1 = e2.
Proof.
  intros; eapply elab_ta_deterministic; eauto.
Qed.
  
Lemma elab_args_deterministic l args s1 s2 args' s'
     : all_fresh l ->
       elab_args l args s1 args' s' ->
       elab_args l args s2 args' s' ->
       s1 = s2.
Proof.
  intros; eapply elab_ta_deterministic; eauto.
Qed.

Lemma elab_sort_deterministic l e1 e2 e'
  : all_fresh l ->
    elab_sort l e1 e' ->
    elab_sort l e2 e' ->
    e1 = e2.
Proof.
  induction 2; inversion 1;
    try match goal with
          [allf : is_true(all_fresh ?l),
                  H1 : is_true((?n,_) \in ?l),
                       H2 : is_true((?n,_) \in ?l) |-_]=>
          let H' := fresh in
          pose proof (in_all_fresh_same allf H1 H2) as H';
            inversion H'
        end;subst; repeat f_equal; eauto using elab_args_deterministic.
Qed.

Lemma elab_ctx_deterministic l c1 c'
  : all_fresh l ->
    elab_ctx l c1 c' ->
    forall c2,
      elab_ctx l c2 c' ->
      c1 = c2.
Proof.
  induction 2; inversion 1; break; subst;
    simpl; repeat f_equal; eauto using elab_sort_deterministic with pfcore.
Qed.


Lemma elab_rule_deterministic l r1 r2 r'
  : all_fresh l ->
    elab_rule l r1 r' ->
    elab_rule l r2 r' ->
    r1 = r2.
Proof.
  inversion 2; inversion 1; break; subst;
    simpl; repeat f_equal;
      eauto using elab_ctx_deterministic,
      elab_term_deterministic,
      elab_sort_deterministic with pfcore.
Qed.


Lemma elab_term_total l' c' e' t'
  : wf_term l' c' e' t' -> exists e, elab_term l' e e'.
Proof.
Admitted.
Hint Resolve elab_term_total : pfcore.

Lemma elab_sort_total l' c' t'
  : wf_sort l' c' t' -> exists t, elab_sort l' t t'.
Proof.
Admitted.
Hint Resolve elab_sort_total : pfcore.

Lemma elab_ctx_total l' c'
  : wf_ctx l' c' -> exists c, elab_ctx l' c c'.
Proof.
Admitted.
Hint Resolve elab_ctx_total : pfcore.

Lemma elab_rule_monotonicity l' r r' n r0
  : elab_rule l' r r' -> 
    elab_rule ((n,r0)::l') r r'.
Proof.
Admitted.
Hint Resolve elab_rule_monotonicity : pfcore.

Lemma elab_lang_in l l' name r'
  : elab_lang l l' ->
    (name, r')\in l' ->
    exists r, (name,r)\in l /\ elab_rule l' r r'.
Proof.
  induction 1; pfcore_crush.
  {
    (*TODO:...why doesn't rewrite work?*)
    setoid_rewrite pair_equal_spec in H3.
    exists r; pfcore_crush.
  }
  {
    destruct H2 as [r0 [r0in elabr0]].
    exists r0; pfcore_crush.
  }
Qed.

Ltac unify_deterministic_elabs :=
  repeat match goal with
    | [elab : elab_lang _ ?l,
       H1 : elab_sort ?l _ ?t',
       H2 : elab_sort ?l _ ?t' |-_] => 
      pose proof (elab_sort_deterministic (elab_lang_all_fresh elab) H1 H2);
        clear H2
    | [elab : elab_lang _ ?l,
       H1 : elab_ctx ?l _ ?t',
       H2 : elab_ctx ?l _ ?t' |-_] => 
      pose proof (elab_ctx_deterministic (elab_lang_all_fresh elab) H1 H2);
        clear H2
    | [elab : elab_lang _ ?l,
       H1 : elab_term ?l _ ?t',
       H2 : elab_term ?l _ ?t' |-_] => 
      pose proof (elab_term_deterministic (elab_lang_all_fresh elab) H1 H2);
        clear H2
    end.
  


Lemma elab_sort_subst_is_subst l t s' t'
  : elab_sort l t (wfexp_subst s' t') ->
    exists t1 s1, t = t1[/s1/]
                  /\ elab_sort l t1 t'
                  /\ elab_subst l s1 s'.
Proof.
Admitted.

(*TODO: doesn't quite work due to convs *)
(*TODO: the inverse is desirable, but with implicit args,
  the best we can do is this:
  ImCore.le_sort t1 t2 ->
  exists t1' t2',
      elab t1 t1' ->
      elab t2 t2' ->
      Core.le_sort t1' t2'
  
  While this is useful, compiler lemmas
  are somewhat unsatisfactory due to computing
  on t1' and t2'.
  Is it fine to just focus on the elaborated/no implicits

*)
Lemma pfcore_wf_imcore_wf l l'
  : elab_lang l l' ->
    wf_lang l' ->
    (forall c' p t1' t2',
        PfCoreDefs.le_sort l' c' p t1' t2' ->
        forall c t1 t2,
          elab_ctx l' c c' ->
          elab_sort l' t1 t1' ->
          elab_sort l' t2 t2' ->
          ImCore.le_sort l c t1 t2)
    /\ (forall c' p t' e1' e2',
        PfCoreDefs.le_term l' c' p t' e1' e2' ->
        forall c e1 e2 t,
          elab_ctx l' c c' ->
          elab_term l' e1 e1' ->
          elab_term l' e2 e2' ->
          elab_sort l' t t' ->
          ImCore.le_term l c t e1 e2)
    /\ (forall c' c1' pfs s1' s2',
        PfCoreDefs.le_subst l' c' c1' pfs s1' s2' ->
        forall c c1 s1 s2,
          elab_ctx l' c c' ->
          elab_subst l' s1 s1' ->
          elab_subst l' s2 s2' ->
          elab_ctx l' c1 c1' ->
          ImCore.le_subst l c c1 s1 s2)
    /\ (forall c' t',
        PfCoreDefs.wf_sort l' c' t' ->
        forall c t,
          elab_ctx l' c c' ->
          elab_sort l' t t' ->
          ImCore.wf_sort l c t)
    /\ (forall c' e' t',
        PfCoreDefs.wf_term l' c' e' t' ->
        forall c e t,
          elab_ctx l' c c' ->
          elab_term l' e e' ->
          elab_sort l' t t' ->
          ImCore.wf_term l c e t)
    /\ (forall c' s' c1',
        PfCoreDefs.wf_args l' c' s' c1' ->
        forall c args s c1,
          elab_ctx l' c c' ->
          elab_args l' args s (map fst c') s' ->
          elab_ctx l' c1 c1' ->
          exists es, ImCore.wf_args l c s args es c1)
    /\ (forall c',
        PfCoreDefs.wf_ctx l' c' ->
        forall c,
          elab_ctx l' c c' ->
          ImCore.wf_ctx l c).
Proof.
  intros elab_l wfl.
  apply judge_ind.
  Ltac use_in_elab_lang :=
    match goal with
      [ elab : elab_lang _ ?l,
               Hin : is_true ((_,_) \in ?l)|-_] =>
      let H' := fresh in
      pose proof (elab_lang_in elab Hin) as H';
        let r := fresh "r" in
        let rin := fresh "Hrin" in
        let relab := fresh "relab" in
        destruct H' as [r [rin relab]];
          inversion relab
    end.
  Ltac2 call_with_hyp_and_type t h :=
    match h with
    | (h_id,_, h_ty) => t h_id h_ty
    end.
  Ltac2 for_each_hyp t :=
    List.iter ( call_with_hyp_and_type t) (Control.hyps ()).

  Require Import Ltac2.Ltac2.
  Ltac expand_hyps :=
     ltac2:(for_each_hyp
             (fun h_id t =>
                let h := (Control.hyp h_id) in
                match! t with
                | elab_sort _ _ (wfexp_subst _ _) =>
                  Std.pose None '(elab_sort_subst_is_subst $h)
                | le_sort ?l _ _ _ _ =>
                  match! goal with
                  | [wfl : wf_lang ?l'|-_]=>
                    (*TODO: Std.unify l l';*)
                    let wfl := (Control.hyp wfl) in
                    Std.pose None '(le_sort_l_wf $wfl $h);
                    Std.pose None '(le_sort_r_wf $wfl $h)
                  end
                | wf_sort _ _ _ =>
                  let h' := Fresh.in_goal h_id in
                  Message.print (Message.of_ident h');
                  Std.pose (Some h') '(elab_sort_total $h)
                | wf_ctx _ _ =>
                  let h' := Fresh.in_goal h_id in
                  Message.print (Message.of_ident h');
                  Std.pose (Some h') '(elab_ctx_total $h)
                  (*
                  let h'' := (Control.hyp h') in
                  try (destruct h'')*)
                | _ => ()(*Message.print (Message.of_ident h_id)*)
                end
                  
          )).
  
  all: try solve [intros; try use_in_elab_lang;
    unify_deterministic_elabs; subst;
      eauto with imcore].
  {
    intros.
    expand_hyps.
    firstorder; subst; eauto with imcore.
  }
  {
    intros.
    expand_hyps.
    (*TODO: how to saturate hyps?*)
    expand_hyps.
    firstorder eauto with imcore.
  }
  {
    intros.
    expand_hyps.
    firstorder; subst.
    admit
    (*term subst case; same as above*).
  }
  {
    intros.
    admit (* term trans case; same as above *).
  }
  {
    intros.
    safe_invert H4.
    safe_invert H5.
    assert (wf_sort l' c t).
    admit.
    pose proof (elab_sort_total H4).
    firstorder eauto with imcore.
  }
