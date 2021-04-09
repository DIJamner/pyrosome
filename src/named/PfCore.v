Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From Utils Require Import Utils BoolAsProp.
From Named Require Import Pf.
From Named Require Export PfCoreDefs.
Import OptionMonad.

Require Import String.


(*TODO: where is the right place for these? Utils rewrite base?*)
Hint Rewrite in_cons : utils.
Hint Rewrite pair_equal_spec : utils.

(*TODO: mvoe to Utils *)
(*TODO: put in utils, add nil lemma *)
Lemma fresh_cons A n m (e:A) es : fresh n ((m,e)::es) <-> (~ n = m) /\ fresh n es.
Proof.
  repeat (simpl in *; autorewrite with bool_utils utils in * ); intuition auto.
Qed.
Hint Rewrite fresh_cons : utils.
Arguments fresh : simpl never.

(*TODO: move to utils/rewriting package*)
Lemma invert_list_Forall_nil A (P : A -> Prop)
  : List.Forall P [::] <-> True.
Proof.
  intuition; intro H; safe_invert H.
Qed.
Hint Rewrite invert_list_Forall_nil : utils.
Lemma invert_list_Forall_cons A (P : A -> Prop) a l
  : List.Forall P (a::l) <-> P a /\ List.Forall P l.
Proof.
  intuition;
  safe_invert H; auto.  
Qed.
Hint Rewrite invert_list_Forall_cons : utils.
  
Lemma wf_lang_all_fresh l : wf_lang l -> all_fresh l.
Proof.
  induction l; break; simpl in *;
    intro H; inversion H; subst; break_goal; auto.
Qed.
Hint Resolve wf_lang_all_fresh : pfcore.
  

(*TODO: move to PfCore*)
Lemma invert_wf_lang_cons l r n
  : wf_lang ((n,r)::l) <-> wf_lang l /\ wf_rule l r /\ fresh n l.
Proof.  
  intuition; try inversion H; eauto with pfcore.
Qed.
Hint Rewrite invert_wf_lang_cons : pfcore.


Lemma invert_wf_rule_sort l c args
  : wf_rule l (Pf.wf_sort_rule c args) <-> wf_ctx l c /\ subseq args (map fst c).
Proof.  
  intuition; try inversion H; eauto with pfcore.
Qed.
Hint Rewrite invert_wf_rule_sort : pfcore.

Lemma invert_wf_rule_term l c args t
  : wf_rule l (Pf.wf_term_rule c args t) <-> wf_ctx l c /\ wf_sort l c t /\ subseq args (map fst c).
Proof.  
  intuition; try inversion H; eauto with pfcore.
Qed.
Hint Rewrite invert_wf_rule_term : pfcore.

Lemma invert_wf_rule_le_sort l c t1 t2
  : wf_rule l (Pf.wf_sort_le c t1 t2) <-> wf_ctx l c /\ wf_sort l c t1 /\ wf_sort l c t2.
Proof.  
  intuition; try inversion H; eauto with pfcore.
Qed.
Hint Rewrite invert_wf_rule_le_sort : pfcore.

Lemma invert_wf_rule_le_term l c t e1 e2
  : wf_rule l (Pf.wf_term_le c e1 e2 t) <->
    wf_ctx l c /\ wf_sort l c t /\ wf_term l c e1 t /\ wf_term l c e2 t.
Proof.  intuition; try inversion H; eauto with pfcore. Qed.
Hint Rewrite invert_wf_rule_le_term : pfcore.

Lemma invert_rule_eq_sort_term c args c' args' t'
  : Pf.wf_sort_rule c args = Pf.wf_term_rule c' args' t' <-> False.
Proof.  intuition; try inversion H; eauto with pfcore. Qed.
Hint Rewrite invert_rule_eq_sort_term : pfcore.


Lemma invert_rule_eq_sort_le_term c t1 t2 c' args' t'
  : Pf.wf_sort_le c t1 t2 = Pf.wf_term_rule c' args' t' <-> False.
Proof.  intuition; try inversion H; eauto with pfcore. Qed.
Hint Rewrite invert_rule_eq_sort_le_term : pfcore.

Lemma invert_rule_eq_sort_le_sort c t1 t2 c' args'
  : Pf.wf_sort_le c t1 t2 = Pf.wf_sort_rule c' args' <-> False.
Proof.  intuition; try inversion H; eauto with pfcore. Qed.
Hint Rewrite invert_rule_eq_sort_le_sort : pfcore.

Lemma invert_rule_eq_sort_le_term_le c t1 t2 c' t' e1' e2'
  : Pf.wf_sort_le c t1 t2 = Pf.wf_term_le c' t' e1' e2' <-> False.
Proof.  intuition; try inversion H; eauto with pfcore. Qed.
Hint Rewrite invert_rule_eq_sort_le_term_le : pfcore.

Lemma invert_rule_eq_sort_le c t1 t2 c' t1' t2'
  : Pf.wf_sort_le c t1 t2 = Pf.wf_sort_le c' t1' t2' <-> c = c' /\ t1 = t1' /\ t2 = t2'.
Proof. intuition; try inversion H; repeat f_equal; eauto with pfcore. Qed.
Hint Rewrite invert_rule_eq_sort_le : pfcore.


Lemma invert_rule_eq_term_le_term c e1 e2 t c' args' t'
  : Pf.wf_term_le c e1 e2 t = Pf.wf_term_rule c' args' t' <-> False.
Proof.  intuition; try inversion H; eauto with pfcore. Qed.
Hint Rewrite invert_rule_eq_term_le_term : pfcore.

Lemma invert_rule_eq_term_le_sort c e1 e2 t c' args'
  : Pf.wf_term_le c e1 e2 t = Pf.wf_sort_rule c' args' <-> False.
Proof. intuition; try inversion H; eauto with pfcore. Qed.
Hint Rewrite invert_rule_eq_term_le_sort : pfcore.

Lemma invert_rule_eq_term_le_sort_le c e1 e2 t c' t1' t2'
  : Pf.wf_term_le c e1 e2 t = Pf.wf_sort_le c' t1' t2' <-> False.
Proof.  intuition; try inversion H; eauto with pfcore. Qed.
Hint Rewrite invert_rule_eq_term_le_sort_le : pfcore.

Lemma invert_rule_eq_term_le c e1 e2 t c' e1' e2' t'
  : Pf.wf_term_le c e1 e2 t = Pf.wf_term_le c' e1' e2' t'
    <-> c = c' /\ t = t' /\ e1 = e1' /\ e2 = e2'.
Proof. intuition; try inversion H; repeat f_equal; eauto with pfcore. Qed.
Hint Rewrite invert_rule_eq_term_le : pfcore.

Ltac pfcore_crush :=
  repeat (simpl; autorewrite with utils bool_utils pfcore in *; intuition (subst; eauto with pfcore)).

Local Lemma lang_mono l name r
  : (forall c p t1 t2,
        le_sort l c p t1 t2 ->
        le_sort ((name,r)::l) c p t1 t2)
    /\ (forall c p t e1 e2,
           le_term l c p t e1 e2 ->
           le_term ((name,r)::l) c p t e1 e2)
    /\ (forall c c' pfs s1 s2,
           le_subst l c c' pfs s1 s2 ->
           le_subst ((name,r)::l) c c' pfs s1 s2)
    /\ (forall c t,
           wf_sort l c t ->
           wf_sort ((name,r)::l) c t)
    /\ (forall c e t,
           wf_term l c e t ->
           wf_term ((name,r)::l) c e t)
    /\ (forall c s c',
           wf_args l c s c' ->
           wf_args ((name,r)::l) c s c')
    /\ (forall c,
           wf_ctx l c ->
           wf_ctx ((name,r)::l) c).
Proof using.
  apply judge_ind;
    intros;
    econstructor;
    pfcore_crush.
Qed.

Definition le_sort_lang_monotonicity l name r
  := proj1 (lang_mono l name r).
#[export] Hint Resolve le_sort_lang_monotonicity : pfcore.

Definition le_term_lang_monotonicity l name r
  := proj1 (proj2 (lang_mono l name r)).
#[export] Hint Resolve le_term_lang_monotonicity : pfcore.

Definition le_subst_lang_monotonicity l name r
  := proj1 (proj2 (proj2 (lang_mono l name r))).
#[export] Hint Resolve le_subst_lang_monotonicity : pfcore.

Definition wf_sort_lang_monotonicity l name r
  := proj1 (proj2 (proj2 (proj2 (lang_mono l name r)))).
#[export] Hint Resolve wf_sort_lang_monotonicity : pfcore.

Definition wf_term_lang_monotonicity l name r
  := proj1 (proj2 (proj2 (proj2 (proj2 (lang_mono l name r))))).
#[export] Hint Resolve wf_term_lang_monotonicity : pfcore.

Definition wf_args_lang_monotonicity l name r
  := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (lang_mono l name r)))))).
#[export] Hint Resolve wf_args_lang_monotonicity : pfcore.

Definition wf_ctx_lang_monotonicity l name r
  := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (lang_mono l name r)))))).
#[export] Hint Resolve wf_ctx_lang_monotonicity : pfcore.

Lemma wf_rule_lang_monotonicity l name r' r
  : wf_rule l r -> wf_rule ((name, r') :: l) r.
Proof.
  inversion 1; pfcore_crush.
Qed.
#[export] Hint Resolve wf_rule_lang_monotonicity : pfcore.

Lemma rule_in_wf l r name
  : wf_lang l -> (name,r) \in l -> wf_rule l r.
Proof.
  induction 1; pfcore_crush.
  (*TODO: why does regular rewrite fail?*)
  setoid_rewrite pair_equal_spec in H3.
  pfcore_crush.
Qed.

Lemma le_subst_subst_monotonicity l c c' c'' pfs s1 s2 pfs' s1' s2'
  : le_subst l c' c'' pfs s1 s2 ->
    le_subst l c c' pfs' s1' s2' ->
    le_subst l c c'' (named_map (pf_subst pfs') pfs)
             (named_map (wfexp_subst s1') s1)
             (named_map (wfexp_subst s2') s2).
Proof.
  induction 1; pfcore_crush.
  constructor; pfcore_crush.
  (*
    TODO: prove subst_assoc
  rewrite wfexp_subst_assoc.
  apply le_term_subst; pfcore_crush. *)
Admitted.
#[export] Hint Resolve le_subst_subst_monotonicity : pfcore.

(*TODO: move to PfCoreDefs *)
Scheme wf_sort_ind'' := Minimality for wf_sort Sort Prop
  with wf_term_ind'' := Minimality for wf_term Sort Prop
  with wf_args_ind'' := Minimality for wf_args Sort Prop.
Combined Scheme wf_ind
         from wf_sort_ind'', wf_term_ind'', wf_args_ind''.

Local Lemma wf_subst_mono l c' s
  : (forall c t,
        wf_sort l c t ->
        wf_subst l c' s c ->
        wf_sort l c' (wfexp_subst s t))
    /\ (forall c e t,
           wf_term l c e t ->
           wf_subst l c' s c ->
           wf_term l c' (wfexp_subst s e) (wfexp_subst s t))
    /\ (forall c s' c'',
           wf_args l c s' c'' ->
           wf_subst l c' s c ->
           wf_args l c' (map (wfexp_subst s) s') c'').
Proof using.
  apply wf_ind;
    intros;
    try econstructor;
    pfcore_crush.
  (*
    TODO: prove subst_assoc*)
Admitted.

Definition wf_sort_subst_monotonicity l name r
  := proj1 (wf_subst_mono l name r).
#[export] Hint Resolve wf_sort_subst_monotonicity : pfcore.

Definition wf_term_subst_monotonicity l name r
  := proj1 (proj2 (lang_mono l name r)).
#[export] Hint Resolve wf_term_subst_monotonicity : pfcore.

Definition wf_args_subst_monotonicity l name r
  := proj1 (proj2 (proj2 (lang_mono l name r))).
#[export] Hint Resolve wf_args_subst_monotonicity : pfcore.



(*TODO: warning; lhs may need a conv for this to be true*)
Lemma le_term_wf l c p e1 e2 t
  : wf_lang l ->
    le_term l c p t e1 e2 ->
    (wf_term l c e1 t /\ wf_term l c e2 t).
Proof.
  intro wfl.
  induction 1; pfcore_crush.
  {
    (*TODO: definitely need a conv on lhs*)
Abort.


Definition le_sort_l_wf l c p t1 t2 wfl les := proj1 (@le_sort_wf l c p t1 t2 wfl les).
Hint Resolve le_sort_l_wf : pfcore.
Definition le_sort_r_wf l c p t1 t2 wfl les := proj2 (@le_sort_wf l c p t1 t2 wfl les).
Hint Resolve le_sort_r_wf : pfcore.

Lemma le_sort_wf l c p t1 t2
  : wf_lang l ->
    le_sort l c p t1 t2 ->
    (wf_sort l c t1 /\ wf_sort l c t2).
Proof.
  intro wfl.
  induction 1; pfcore_crush.
  {
    (*TODO: put in non-repeated crush phase*)
    apply rule_in_wf in H;
    pfcore_crush.
  }
  {
    (*TODO: put in non-repeated crush phase*)
    apply rule_in_wf in H;
    pfcore_crush.
  }
  {
    eapply wf_sort_subst_monotonicity; eauto.
    admit (*TODO: need sim. thms for term, subst*).
  }
  {
    eapply wf_sort_subst_monotonicity; eauto.
    admit (*TODO: need sim. thms for term, subst*).
  }
Admitted.

Definition le_sort_l_wf l c p t1 t2 wfl les := proj1 (@le_sort_wf l c p t1 t2 wfl les).
Hint Resolve le_sort_l_wf : pfcore.
Definition le_sort_r_wf l c p t1 t2 wfl les := proj2 (@le_sort_wf l c p t1 t2 wfl les).
Hint Resolve le_sort_r_wf : pfcore.
