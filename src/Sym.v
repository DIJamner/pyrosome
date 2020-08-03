
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From excomp Require Import Utils Exp Rule Core.

(*TODO: move to core *)
Lemma mono_rule_n l' l r
  : wf_rule l r -> wf_lang (l' ++ l) -> wf_rule (l' ++ l) r.
Proof using .
  case: r; intro_to wf_rule; inversion; subst;
  intros; constructor; eauto with judgment;
  eapply mono_n; eauto with judgment.
Qed.

(*TODO move to dedicated file*)
Definition wf_lang_ext l1 l2 := wf_lang (l1 ++ l2).

Section Shifting.
  Variables shift start : nat.
  
  Fixpoint shift_exp  e : exp :=
    match e with
    | var x => var x
    | con n s =>
      con (if n >= start then n + shift else n)
          (map shift_exp s)
    end.

  Definition shift_subst : subst -> subst :=
    map shift_exp.

  Definition shift_ctx : ctx -> ctx :=
    map shift_exp.

  Definition shift_rule r : rule :=
    match r with
    | sort_rule c => sort_rule (shift_ctx c)
    | term_rule c t => term_rule (shift_ctx c) (shift_exp t)
    | sort_le c t1 t2 => sort_le (shift_ctx c) (shift_exp t1) (shift_exp t2)
    | term_le c e1 e2 t => term_le (shift_ctx c) (shift_exp e1) (shift_exp e2) (shift_exp t)
    end.

  Definition shift_lang : lang -> lang := map shift_rule.
  
End Shifting.

Lemma shift_exp0 start e : shift_exp 0 start e = e.
Proof using .
  elim: e; simpl; auto.
  intros; f_equal.
  {
    case: (start <= n); rewrite ?addn0; done.
  }
  {
    elim: l H; simpl; auto.
    intro_to and; case => ->.
    intros; f_equal; eauto.
  }
Qed.

Lemma shift_expmap0 start s : map (shift_exp 0 start) s = s.
Proof using .
  elim: s; simpl; auto.
  intros; f_equal; eauto using shift_exp0.
Qed.

Lemma shift_rule0 start r : shift_rule 0 start r = r.
Proof using .
  case: r; simpl; intros; f_equal; eauto using shift_exp0, shift_expmap0.
Qed.

Lemma shift_lang0 start l : shift_lang 0 start l = l.
Proof using .
  elim: l; simpl; auto.
  intros; f_equal; eauto using shift_rule0.
Qed.


Lemma shift_exp_sum a b start e
  : shift_exp (a + b) start e
    = shift_exp a (b + start) (shift_exp b start e).
Proof.
  elim: e; simpl; auto.
  intros; f_equal.
  {
    case sltn: (start <= n).
    suff: b + start <= n + b;
      [ move->; by rewrite [a + b]addnC addnA|].
    by rewrite [n + b]addnC leq_add2l.
    give_up.
  }
  {
    elim: l H; simpl; auto.
    intro_to and; case => ->.
    intros; f_equal; eauto.
  }
Admitted.

Lemma shift_expmap_sum a b start s
  : map (shift_exp (a + b) start) s
    = map (shift_exp a (b + start)) (map (shift_exp b start) s).
Proof using .
  elim: s; simpl; auto.
  intros; f_equal; eauto using shift_exp_sum.
Qed.

Lemma shift_rule_sum a b start r
  : shift_rule (a + b) start r
    = shift_rule a (b + start) (shift_rule b start r).
Proof using .
  case: r; simpl; intros; f_equal; eauto using shift_exp_sum, shift_expmap_sum.
Qed.

Lemma shift_lang_sum a b start l
  : shift_lang (a + b) start l
    = shift_lang a (b + start) (shift_lang b start l).
Proof using .
  elim: l; simpl; auto.
  intros; f_equal; eauto using shift_rule_sum.
Qed.  

Lemma shift_lookup_comm a b s n
  : shift_exp a b (var_lookup s n)
    = var_lookup (shift_subst a b s) n.
Proof.
  unfold var_lookup.
  unfold nth_level.
  rewrite !size_map.
  case: (n < size s); simpl; auto.
  symmetry.
  apply: nth_map.
  give_up.
Admitted.
                                                  
Lemma shift_subst_comm a b e s
  : shift_exp a b e[/s/] = (shift_exp a b e)[/shift_subst a b s/].
Proof.
  elim: e; intros; simpl.
  {
    unfold exp_subst; simpl; apply shift_lookup_comm.   
  }
  {
    rewrite con_subst_cmp; f_equal.
    elim: l H; simpl; auto.
    intro_to and; case => ->.
    move /H => ->.
    tauto.
  }      
Qed.

Lemma wf_term_insert l l1 l2 c e t
  : (*TODO: needed?
      wf_lang_ext ((shift_lang (size l2) (size l) l1) ++ l2) l ->*)
    wf_term (l1 ++ l) c e t ->
    wf_term ((shift_lang (size l2) (size l) l1) ++ l2 ++ l)
            (shift_ctx (size l2) (size l) c)
            (shift_exp (size l2) (size l) e)
            (shift_exp (size l2) (size l) t).
Proof.
  elim; simpl.
  {
    intros.
    rewrite shift_subst_comm.
    apply: wf_term_by'.
    instantiate (1:=shift_ctx (size l2) (size l) c').
    give_up.
    TODO: needs to be a big mutual thm
  
Lemma wf_sort_insert l l1 l2 c t
  : (*TODO: needed?
      wf_lang_ext ((shift_lang (size l2) (size l) l1) ++ l2) l ->*)
    wf_sort (l1 ++ l) c t ->
    wf_sort ((shift_lang (size l2) (size l) l1) ++ l2 ++ l)
            (shift_ctx (size l2) (size l) c)
            (shift_exp (size l2) (size l) t).
Proof.

Lemma wf_lang_ext_merge l l1 l2
  : wf_lang_ext l1 l ->
    wf_lang_ext l2 l ->
    wf_lang_ext ((shift_lang (size l2) (size l) l1) ++ l2) l.
Proof.
  move: l2 l1 l.
  unfold wf_lang_ext.
  apply: List.rev_ind; simpl.
  {
    intros; by rewrite shift_lang0 cats0.
  }
  
  intro_to wf_lang.
  rewrite -!catA size_cat shift_lang_sum; simpl.
  intros.

  change (1 + size l0) with (size (x::l0)).
  rewrite [_++ l ++ _]catA.
  eapply H; auto.

  move: H1 => /wf_lang_prefix H1.
  clear H l.
  inversion H1; subst.
  elim: l1 H0; simpl; auto.
  intros.
  apply: wf_lang_cons'.
  inversion H0; subst.
  move: (H H6) => H8.

  clear H6 H0 H.
  case: a H7; simpl; intros; constructor; eauto with judgment.
  
  change (x::l0) with ([::x]++l0).
  apply: H.
  TODO: lemma?
  
Qed.

TODO: language permutations are in bijection

Definition symmetric_rels : lang -> lang :=
  pmap (fun r =>
  match r with
  | (sort_rule _)
  | (term_rule _ _) => None
  | (sort_le c t1 t2) => Some (sort_le c t2 t1)
  | (term_le c e1 e2 t) => Some (term_le c e2 e1 t)
  end).

