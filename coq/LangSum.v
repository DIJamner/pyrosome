Load Core.

Lemma rule_app_l_mono {p} (l1 l2 : lang p) r
  : wf_rule l1 r -> wf_lang (l2 ++ l1) -> wf_rule (l2 ++ l1) r.
Proof.
  move => wfr.
  elim: l2; auto.
  move => r' l2 IH.
  rewrite cat_cons => wflr.
  inversion wflr.
  apply: wf_rule_mono; auto.
  apply: IH.
  apply: wf_rule_lang; eauto.
Qed.

Scheme le_sort_ind' := Minimality for le_sort Sort Prop
  with le_subst_ind' := Minimality for le_subst Sort Prop
  with le_term_ind' := Minimality for le_term Sort Prop
  with le_ctx_ind' := Minimality for le_ctx Sort Prop
  with le_ctx_var_ind' := Minimality for le_ctx_var Sort Prop
  with wf_sort_ind' := Minimality for wf_sort Sort Prop
  with wf_subst_ind' := Minimality for wf_subst Sort Prop
  with wf_term_ind' := Minimality for wf_term Sort Prop
  with wf_ctx_ind' := Minimality for wf_ctx Sort Prop
  with wf_ctx_var_ind' := Minimality for wf_ctx_var Sort Prop
  with wf_rule_ind' := Minimality for wf_rule Sort Prop
  with wf_lang_ind' := Minimality for wf_lang Sort Prop.

Combined Scheme all_lang_ind from
         le_sort_ind',
         le_subst_ind',
         le_term_ind',
         le_ctx_ind',
         le_ctx_var_ind',
         wf_sort_ind',
         wf_subst_ind',
         wf_term_ind',
         wf_ctx_ind',
         wf_ctx_var_ind',
         wf_rule_ind',
         wf_lang_ind'.

Lemma mono_cat {p} l2 (wfl : wf_lang l2)
  : (forall (l : lang p) c1 c2 t1 t2,
        le_sort l c1 c2 t1 t2 -> le_sort (l++l2) c1 c2 t1 t2)
    /\ (forall (l : lang p) c1 c2 s1 s2 c1' c2',
           le_subst l c1 c2 s1 s2 c1' c2' ->
           le_subst (l++l2) c1 c2 s1 s2 c1' c2')
    /\ (forall (l : lang p) c1 c2 e1 e2 t1 t2,
           le_term l c1 c2 e1 e2 t1 t2 ->
           le_term (l++l2) c1 c2 e1 e2 t1 t2)
    /\ (forall (l : lang p) c1 c2,  le_ctx l c1 c2 -> le_ctx (l++l2) c1 c2)
    /\ (forall (l : lang p) c1 c2 v1 v2,
           le_ctx_var l c1 c2 v1 v2 -> le_ctx_var (l++l2) c1 c2 v1 v2)
    /\ (forall (l : lang p) c t, wf_sort l c t -> wf_sort (l++l2) c t)
    /\ (forall (l : lang p) c s c', wf_subst l c s c' -> wf_subst (l++l2) c s c')
    /\ (forall (l : lang p) c e t,  wf_term l c e t-> wf_term (l++l2) c e t)
    /\ (forall (l : lang p) c,  wf_ctx l c -> wf_ctx (l++l2) c)
    /\ (forall (l : lang p) c v,  wf_ctx_var l c v -> wf_ctx_var (l++l2) c v)
    /\ (forall (l : lang p) r,  wf_rule l r -> wf_rule (l++l2) r)
    /\ (forall (l : lang p),  wf_lang l -> wf_lang (l++l2)).
Proof.
  apply: all_lang_ind; eauto using List.in_or_app.
  - constructor; auto.    
Qed.

(*TODO: write all the various corrolaries *)

