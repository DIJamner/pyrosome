Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From Utils Require Import Utils.
From Named Require Import Core (*TODO: remove dependency*) Exp ARule Pf.

Require Import String.


Create HintDb imcore discriminated.

Section TermsAndRules.
  Context (l : lang).

  (*These use Exp and ARule for inferred terms
    I have yet to use ann, so maybe give it up for now?
   *)
  
  Inductive le_sort c : sort -> sort -> Prop :=
  | le_sort_by : forall name t1 t2,
      (name, sort_le c t1 t2) \in l ->
      le_sort c t1 t2
  | le_sort_subst : forall s1 s2 c' t1' t2',
      (* TODO: this breaks le_sort's assumptions;
         Need to assert wf_ctx c'?
         Would have to be mutual.
         That would give me a big circularity;
         better to have wf_ctx' that uses refl
       *)
      le_subst c c' s1 s2 ->
      le_sort c' t1' t2' ->
      le_sort c t1'[/s1/] t2'[/s2/]
  | le_sort_con : forall name c' args s1 s2 es1 es2,
      (name, (sort_rule c' args)) \in l ->
      le_args c c' s1 s2 args es1 es2 ->
      le_sort c (scon name s1) (scon name s2)
  | le_sort_trans : forall t1 t12 t2,
      le_sort c t1 t12 ->
      le_sort c t12 t2 ->
      le_sort c t1 t2
  | le_sort_sym : forall t1 t2, le_sort c t1 t2 -> le_sort c t2 t1
  with le_term c : sort -> exp -> exp -> Prop :=
  | le_term_subst : forall s1 s2 c' t e1 e2,
      le_subst c c' s1 s2 ->
      le_term c' t e1 e2 ->
      le_term c t[/s2/] e1[/s1/] e2[/s2/]
  | le_term_by : forall name t e1 e2,
      (name,term_le c e1 e2 t) \in l ->
                                   le_term c t e1 e2
  | le_term_con : forall name c' args t s1 s2 es1 es2,
      (*TODO: use le_args here? makes things more mutual.*)
      (name, (term_rule c' args t)) \in l ->
                                        le_args c c' s1 s2 args es1 es2 ->
                                        le_term c t[/with_names_from c' es2/] (con name s1) (con name s2)
  | le_term_var : forall x t,
      (x,t) \in c ->
                le_term c t (var x) (var x)
  | le_term_trans : forall t e1 e12 e2,
      le_term c t e1 e12 ->
      le_term c t e12 e2 ->
      le_term c t e1 e2
  | le_term_sym : forall t e1 e2, le_term c t e1 e2 -> le_term c t e2 e1
  (* Conversion:

c |- e1 = e2 : t 
               ||
c |- e1 = e2 : t'
   *)
  | le_term_conv : forall t t',
      le_sort c t t' ->
      forall e1 e2,
        le_term c t e1 e2 ->
        le_term c t' e1 e2
  (* TODO: do I want to allow implicit elements in substitutions? *)
  (* TODO: do I want to define this in terms of le_args? *)
  with le_subst c : ctx -> subst -> subst -> Prop :=
  | le_subst_nil : le_subst c [::] [::] [::]
  | le_subst_cons : forall c' s1 s2,
      le_subst c c' s1 s2 ->
      forall name t e1 e2,
        (* assumed because the output ctx is wf: fresh name c' ->*)
        le_term c t[/s2/] e1 e2 ->
        le_subst c ((name, t)::c') ((name,e1)::s1) ((name,e2)::s2)
  with le_args c : ctx -> list exp -> list exp -> list string -> list exp -> list exp -> Prop :=
  | le_args_nil : le_args c [::] [::] [::] [::] [::] [::]
  | le_args_cons_ex : forall c' s1 s2 args es1 es2,
      le_args c c' s1 s2 args es1 es2 ->
      forall name t e1 e2,
        (* assumed because the output ctx is wf: fresh name c' ->*)
        le_term c t[/with_names_from c' es2/] e1 e2 ->
        le_args c ((name, t)::c') (e1::s1) (e2::s2) (name::args) (e1::es1) (e2::es2)
  | le_args_cons_im : forall c' s1 s2 args es1 es2,
      le_args c c' s1 s2 args es1 es2 ->
      forall name t e1 e2,
        (* assumed because the output ctx is wf: fresh name c' ->*)
        le_term c t[/with_names_from c' es2/] e1 e2 ->
        le_args c ((name, t)::c') s1 s2 args (e1::es1) (e2::es2).

  Hint Constructors le_sort le_term le_subst le_args : imcore.

  Inductive wf_term c : exp -> sort -> Prop :=
  | wf_term_by : forall n s args es c' t,
      (n, term_rule c' args t) \in l ->
                                   wf_args c s args es c' ->
                                   wf_term c (con n s) t[/(with_names_from c' es)/]
  | wf_term_conv : forall e t t',
      (* We add this condition so that we satisfy the assumptions of le_sort *)
      wf_sort c t -> 
      wf_term c e t ->
      le_sort c t t' ->
      wf_term c e t'
  | wf_term_var : forall n t,
      (n, t) \in c ->
                 wf_term c (var n) t
  with wf_args c : list exp -> list string -> list exp -> ctx -> Prop :=
  | wf_args_nil : wf_args c [::] [::] [::] [::]
  | wf_args_cons_ex : forall s args es c' name e t,
      fresh name c' ->
      wf_term c e t[/with_names_from c' es/] ->
      (* these arguments are last so that proof search unifies existentials
       from the other arguments first*)
      wf_args c s args es c' ->
      wf_sort c' t ->
      wf_args c (e::s) (name::args) (e::es) ((name,t)::c')
  | wf_args_cons_im : forall s args es c' name e t,
      fresh name c' ->
      wf_term c e t[/with_names_from c' es/] ->
      (* these arguments are last so that proof search unifies existentials
       from the other arguments first*)
      wf_args c s args es c' ->
      wf_sort c' t ->
      wf_args c s args (e::es) ((name,t)::c')
  with wf_sort c : sort -> Prop :=
  | wf_sort_by : forall n s args es c',
      (n, (sort_rule c' args)) \in l ->
                                   wf_args c s args es c' ->
                                   wf_sort c (scon n s).

  Inductive wf_subst c : subst -> ctx -> Prop :=
  | wf_subst_nil : wf_subst c [::] [::]
  | wf_subst_cons : forall s c' name e t,
      (* assumed because the output ctx is wf: fresh name c' ->*)
      wf_subst c s c' ->
      wf_term c e t[/s/] ->
      wf_subst c ((name,e)::s) ((name,t)::c').

  Hint Constructors wf_sort wf_term wf_subst wf_args : imcore.

  Inductive wf_ctx : ctx -> Prop :=
  | wf_ctx_nil : wf_ctx [::]
  | wf_ctx_cons : forall name c v,
      fresh name c ->
      wf_ctx c ->
      wf_sort c v ->
      wf_ctx ((name,v)::c).
  Hint Constructors wf_ctx : imcore.

  Lemma le_term_refl c e t
    : wf_term c e t -> le_term c t e e
  with le_args_refl c s args es c'
       : wf_args c s args es c' -> le_args c c' s s args es es.
  Proof using.
    {
      intro wft; inversion wft; clear wft.
      eapply le_term_con; eauto.
      eapply le_term_conv; eauto.
      eapply le_term_var; auto.
    }
    {
      intro wfa; inversion wfa; clear wfa.
      eapply le_args_nil; auto.
      eapply le_args_cons_ex; auto.
      eapply le_args_cons_im; auto.
    }
  Qed.
  (* TODO: show other direction*)

  Lemma le_sort_refl c t
    : wf_sort c t -> le_sort c t t.
  Proof using.
    intro wft; inversion wft; clear wft.
    eauto using le_args_refl with imcore.
  Qed.
  (* TODO: show other direction*)

  
  Lemma le_subst_refl c s c'
    : wf_subst c s c' -> le_subst c c' s s.
  Proof using.
    intro wft; induction wft;
    eauto using le_term_refl with imcore.
  Qed.

  
  Lemma le_subst_from_args c c' al1 al2 args el1 el2
    : le_args c c' al1 al2 args el1 el2 ->
      le_subst c c' (with_names_from c' el1) (with_names_from c' el2).
  Proof.
    intro leargs; induction leargs; eauto with imcore.
  Qed.
  Hint Resolve le_subst_from_args : imcore.

    
  Lemma wf_subst_from_args c c' al args el
    : wf_args c al args el c' ->
      wf_subst c (with_names_from c' el) c'.
  Proof.
    intro leargs; induction leargs; eauto with imcore.
  Qed.
  Hint Resolve wf_subst_from_args : imcore.

  Hint Resolve named_list_lookup_err_in : imcore.

  (*
  Lemma le_args_shortened_universal_l
    : le_args c c' al1 al2 args el1 el2 ->
      Some al1 = get_subseq args (with_names_from c' el1)*)
  
  Lemma get_subseq_exact (s : subst)
    : Some s = get_subseq (map fst s) s.
  Proof.
    induction s; intros; break; simpl in *; auto.
    rewrite ?eq_refl.
    rewrite <-IHs; eauto.
  Qed.

  
  Lemma synth_le_args_size_l l0 l1 l2 c c0
    : Some (l1, l2) = synth_le_args (synth_le_term l) l0 c c0 ->
      size l1 = size c0.
  Proof.
    revert l1 l2 c0.
    induction l0; intros; destruct c0; break; simpl in *; try by (inversion H; subst; auto).
    revert H.
    case_match; [| intro H; inversion H];
    break.
    case_match; [| intro H; inversion H];
    break.
    case_match; [| intro H; inversion H];
      break.
    symmetry in HeqH1.
    case.
    move: HeqH1 => /eqP.
    intros.
    subst.
    simpl.
    f_equal; eauto.
  Qed.

  Lemma synth_le_args_size_r l0 l1 l2 c c0
    : Some (l1, l2) = synth_le_args (synth_le_term l) l0 c c0 ->
      size l2 = size c0.
  Proof.
    revert l1 l2 c0.
    induction l0; intros; destruct c0; break; simpl in *; try by (inversion H; subst; auto).
    revert H.
    case_match; [| intro H; inversion H];
    break.
    case_match; [| intro H; inversion H];
    break.
    case_match; [| intro H; inversion H];
      break.
    symmetry in HeqH1.
    case.
    move: HeqH1 => /eqP.
    intros.
    subst.
    simpl.
    f_equal; eauto.
  Qed.

  Lemma le_subst_names_eq_r c c' s1 s2
    : le_subst c c' s1 s2 -> map fst s2 = map fst c'.
  Proof using.
    intro les; induction les; auto.
    simpl; f_equal; auto.
  Qed.

  
  Lemma le_subst_subst_monotonicity c c' s1 s2 c'' s1' s2'
       : le_subst c c' s1 s2 -> ws_ctx c' ->
             le_subst c'' c s1' s2' ->
             le_subst c'' c' s1[/s1'/] s2[/s2'/].
  Proof using.
    intro les; induction les; simpl;
      intros; break; simpl; eauto with imcore.
    constructor; fold_Substable; eauto with imcore.
    rewrite <- subst_assoc; eauto with imcore.
    erewrite le_subst_names_eq_r; eauto with imcore.
  Qed.
    
  Lemma le_args_subst_monotonicity c c' al1 al2 args el1 el2 c'' s1 s2
       : le_args c c' al1 al2 args el1 el2 -> ws_ctx c' ->
         le_subst c'' c s1 s2 -> le_args c'' c' al1[/s1/] al2[/s2/] args el1[/s1/] el2[/s2/].
  Proof using.
    intro les; induction les; simpl;
      intros; break; simpl; eauto with imcore;
      constructor; fold_Substable; eauto with imcore;
      rewrite with_names_from_args_subst;
      rewrite <- subst_assoc; eauto with imcore;
      erewrite le_subst_names_eq_r; eauto with imcore;
        eapply le_subst_from_args; eauto with imcore.
  Qed.

 
  Lemma le_subst_id c c'
    :  subseq c c' ->
       le_subst c' c (id_subst [seq i.1 | i <- c]) (id_subst [seq i.1 | i <- c]).
  Proof using.
    elim: c; intros; simpl in *; break; simpl in *;
      constructor.
    apply H.
    eapply subseq_cons_rest; eauto.
    rewrite id_subst_reduce_sort.
    eapply le_term_var.
    eapply subseq_cons_first; eauto.
  Qed.
  
  Lemma wf_sort_is_ws c t
    : wf_sort c t -> well_scoped (map fst c) t
  with wf_term_is_ws c e t
    : wf_term c e t -> well_scoped (map fst c) e
  with wf_args_is_ws c al args el c'
       : wf_args c al args el c' -> well_scoped (map fst c) al.
  Proof using.
    {
      intro wfs; destruct wfs; simpl; eauto with imcore.
    }
    {
      intro wfs; destruct wfs; simpl; eauto with imcore.
      eapply wf_args_is_ws; eauto with imcore.
      eapply pair_fst_in; eauto.
    }
    {
      intro wfs; destruct wfs; simpl; eauto with imcore.
      apply /andP; split; eauto with imcore.
    }
  Qed.

  Hint Resolve wf_sort_is_ws wf_term_is_ws wf_args_is_ws : imcore.

  
  Lemma wf_ctx_is_ws c
    : wf_ctx c -> ws_ctx c.
  Proof.
    intro wfr; induction wfr; simpl; break_goal; eauto with imcore.
  Qed.

  Hint Resolve wf_ctx_is_ws : imcore.

  Lemma wf_subst_names_eq c s c'
    : wf_subst c s c' -> map fst s = map fst c'.
  Proof using.
    intro wfs; induction wfs; simpl; f_equal; eauto with imcore.
  Qed.

  Lemma wf_subst_is_ws c s c'
    : wf_subst c s c' -> all_fresh c' -> well_scoped (map fst c) s.
  Proof using.
    intro wfs; induction wfs; simpl; auto.
    move /andP => []; intros;
    repeat (apply /andP; split); eauto using wf_term_is_ws with imcore.
    erewrite wf_subst_names_eq; eauto.
  Qed.

  Lemma wf_args_size c al args el c'
    : wf_args c al args el c' -> size el = size c'.
  Proof using.
    intro wfa; induction wfa; simpl; f_equal; eauto.
  Qed.

  
  Lemma wf_subst_lookup c' s c n t
    : wf_subst c' s c ->
      ws_ctx c ->
      (n,t)\in c ->
      wf_term c' (subst_lookup s n) t [/s /].
  Proof using.
    intro wfs; revert n t; induction wfs;
      eauto with imcore; simpl.
    intros n t' wsc; break.
    rewrite in_cons.
    change ((n,t')==(name,t)) with ((n=?name)%string && (t'==t)).
    case neq:(n=?name)%string;simpl.
    move: neq=> /eqP -> /orP [].
    {
      move /eqP => ->.
      rewrite ws_sort_mono; eauto with imcore.
      erewrite <-wf_subst_names_eq in wsc1; eassumption.
      erewrite wf_subst_names_eq; eauto.
    }
    {
      intro namein.
      exfalso.
      apply pair_fst_in in namein.
      rewrite namein in wsc1.
      inversion wsc1.
    }
    {
      intro nin.
      rewrite ws_sort_mono; eauto with imcore.
      erewrite <-wf_subst_names_eq in wsc1; eassumption.
      erewrite wf_subst_names_eq; eauto.
      eapply sort_in_ws; eauto.
    }
  Qed.
        
  Lemma wf_sort_subst_monotonicity c t c' s
    : ws_lang l ->
      ws_ctx c ->
      wf_sort c t ->
      wf_subst c' s c ->
      wf_sort c' t[/s/]
  with wf_term_subst_monotonicity c e t c' s
       : ws_lang l ->
         ws_ctx c ->
         wf_term c e t ->
         wf_subst c' s c ->
         wf_term c' e[/s/] t[/s/]
  with wf_args_subst_monotonicity c al args el c' c'' s
       : ws_lang l ->
         ws_ctx c ->
         ws_ctx c' ->
         wf_args c al args el c' ->
         wf_subst c'' s c ->
         wf_args c'' al[/s/] args el[/s/] c'.
  Proof.
    {
      intros wsl wsc wfs; destruct wfs; intro wfsb; simpl.
      assert (ws_ctx c'0).
      {
        apply rule_in_ws in H; simpl in H; break; eauto.
      }
      eapply wf_sort_by; eauto with imcore.
    }
    {
      intros wsl wsc wft; destruct wft; intro wfsb; simpl.
      {
        (*TODO: fix; should work here. fold_Substable.*)
        rewrite subst_assoc.
        rewrite <-with_names_from_args_subst.
        eapply wf_term_by; eauto with imcore.
        eapply wf_args_subst_monotonicity; eauto with imcore.
        apply rule_in_ws in H; simpl in H; break; eauto.
        rewrite map_fst_with_names_from.
        apply rule_in_ws in H; eauto; simpl in H.
        break; auto.
        eapply wf_args_size; eauto.
      }
      {
        eapply wf_term_conv; eauto with imcore.
        eapply le_sort_subst; eauto with imcore.
        eapply le_subst_refl; auto.
      }
      {
        eapply wf_subst_lookup; eauto with imcore.
      }
    }
    {
      intros wsl wsc wsc' wfs; destruct wfs; intro wfsb; simpl in *; break; constructor;
      fold_Substable; eauto with imcore.
      rewrite with_names_from_args_subst.
      rewrite <-subst_assoc; eauto with imcore.
      erewrite wf_subst_names_eq; eauto with imcore.
      rewrite with_names_from_args_subst.
      rewrite <-subst_assoc; eauto with imcore.
      rewrite map_fst_with_names_from; eauto with imcore.
      eapply wf_args_size; eauto.
    }
  Qed.

  Hint Resolve wf_term_subst_monotonicity : imcore.

  Lemma wf_subst_subst_monotonicity c s c' c'' s'
       : ws_lang l ->
         ws_ctx c ->
         ws_ctx c' ->
         wf_subst c s c' ->
         wf_subst c'' s' c ->
         wf_subst c'' s[/s'/] c'.
  Proof using.
    intros wsl wsc wsc' wfs; induction wfs; intro wfsb; simpl in *; break; constructor;
      fold_Substable; eauto with imcore.
    rewrite <-subst_assoc; eauto with imcore.
    erewrite wf_subst_names_eq; eauto with imcore.
  Qed.

  
  Lemma le_sort_ctx_monotonicity c t1 t2 name t
    : le_sort c t1 t2 ->
      le_sort ((name,t)::c) t1 t2
  with le_term_ctx_monotonicity c t e1 e2 name t'
       : le_term c t e1 e2 ->
         le_term ((name,t')::c) t e1 e2
  with le_subst_ctx_monotonicity c c' s1 s2 name t
       : le_subst c c' s1 s2 ->
         le_subst ((name,t)::c) c' s1 s2
  with le_args_ctx_monotonicity c c' al1 al2 args el1 el2 name t
       : le_args c c' al1 al2 args el1 el2 ->
         le_args ((name,t)::c) c' al1 al2 args el1 el2.
  Proof using.
    {
      intro les; destruct les;
        [| eapply le_sort_subst;eauto with imcore
         | eapply le_sort_con;eauto with imcore
         | eapply le_sort_trans;eauto with imcore
         | eapply le_sort_sym;eauto with imcore].
      replace t1 with t1[/id_subst (map fst c)/] by apply id_subst_reduce_sort.
      replace t2 with t2[/id_subst (map fst c)/] by apply id_subst_reduce_sort.
      eapply le_sort_subst.
      eapply le_subst_id; eauto with imcore.
      apply subseq_l_cons_l.
      eapply le_sort_by;eauto.
    }
    {
      intro letm; destruct letm;
      [eapply le_term_subst;eauto with imcore
      |
      | eapply le_term_con;eauto with imcore
      | eapply le_term_var;eauto with imcore
      | eapply le_term_trans;eauto with imcore
      | eapply le_term_sym;eauto with imcore
      | eapply le_term_conv;eauto with imcore].
      replace t with t[/id_subst (map fst c)/] by apply id_subst_reduce_sort.
      replace e1 with e1[/id_subst (map fst c)/] by apply id_subst_reduce.
      replace e2 with e2[/id_subst (map fst c)/] by apply id_subst_reduce.
      eapply le_term_subst.
      eapply le_subst_id; eauto with imcore.
      apply subseq_l_cons_l.
      eapply le_term_by;eauto.
      rewrite in_cons; apply /orP; right; assumption.
    }
    {
      intro les; destruct les; constructor; eauto with imcore.
    }
    {
      intro lea; destruct lea; constructor; eauto with imcore.
    }
  Qed.

  
  Variant wf_rule : rule -> Prop :=
  | wf_sort_rule : forall c args,
      wf_ctx c ->
      subseq args (map fst c) ->
      wf_rule (sort_rule c args)
  | wf_term_rule : forall c args t,
      wf_ctx c ->
      wf_sort c t ->
      subseq args (map fst c) ->
      wf_rule (term_rule c args t)
  | le_sort_rule : forall c t1 t2,
      wf_ctx c ->
      wf_sort c t1 ->
      wf_sort c t2 ->
      wf_rule (sort_le c t1 t2)
  | le_term_rule : forall c e1 e2 t,
      wf_ctx c ->
      wf_sort c t ->
      wf_term c e1 t ->
      wf_term c e2 t ->
      wf_rule (term_le c e1 e2 t).
  Hint Constructors wf_rule : imcore.

  
  Lemma wf_rule_is_ws r
    : wf_rule r -> ws_rule r.
  Proof using.
    intro wfr; destruct wfr; simpl; break_goal; eauto with imcore.
  Qed.

End TermsAndRules.

Inductive wf_lang : lang -> Prop :=
| wf_lang_nil : wf_lang [::]
| wf_lang_cons : forall l n r,
    fresh n l ->
    wf_lang l ->
    wf_rule l r ->
    wf_lang ((n,r)::l).


Hint Constructors le_sort le_term le_subst le_args
     wf_sort wf_term wf_subst wf_args wf_ctx wf_rule wf_lang : imcore.
Hint Resolve le_subst_refl le_term_refl le_sort_refl le_args_refl : imcore.
Hint Resolve le_subst_from_args wf_subst_from_args : imcore.
Hint Resolve wf_sort_is_ws wf_term_is_ws wf_args_is_ws
     wf_ctx_is_ws wf_rule_is_ws : imcore.
Hint Resolve named_list_lookup_err_in : imcore.
Hint Resolve le_sort_ctx_monotonicity : imcore.
Hint Resolve le_term_ctx_monotonicity : imcore.
Hint Resolve le_subst_ctx_monotonicity : imcore.
Hint Resolve le_args_ctx_monotonicity : imcore.
Hint Resolve wf_sort_subst_monotonicity : imcore.
Hint Resolve wf_term_subst_monotonicity : imcore.
Hint Resolve wf_subst_subst_monotonicity : imcore.
Hint Resolve wf_args_subst_monotonicity : imcore.
Hint Resolve le_subst_subst_monotonicity : imcore.
Hint Resolve le_args_subst_monotonicity : imcore.


Lemma wf_lang_is_ws l
  : wf_lang l -> ws_lang l.
Proof.
  intro wfl; induction wfl; auto.
  unfold ws_lang in IHwfl.
  simpl in *; break;break_goal;
    eauto with imcore.
Qed.

Hint Resolve wf_lang_is_ws : imcore.

Lemma le_sort_lang_monotonicity l c t1 t2 name r
  : le_sort l c t1 t2 ->
    le_sort ((name,r)::l) c t1 t2
with le_term_lang_monotonicity l c t e1 e2 name r
     : le_term l c t e1 e2 ->
       le_term ((name,r)::l) c t e1 e2
with le_subst_lang_monotonicity l c c' s1 s2 name r
     : le_subst l c c' s1 s2 ->
       le_subst ((name,r)::l) c c' s1 s2
with le_args_lang_monotonicity l c c' al1 al2 args el1 el2 name r
     : le_args l c c' al1 al2 args el1 el2 ->
       le_args ((name,r)::l) c c' al1 al2 args el1 el2.
Proof using.
  {
    intro les; destruct les;
      [ eapply le_sort_by; eauto with imcore
      | eapply le_sort_subst;eauto with imcore
      | eapply le_sort_con;eauto with imcore
      | eapply le_sort_trans;eauto with imcore
      | eapply le_sort_sym;eauto with imcore].
    rewrite in_cons; apply /orP; right; eassumption.
    rewrite in_cons; apply /orP; right; eassumption.
  }
  {
    intro letm; destruct letm;
    [eapply le_term_subst;eauto with imcore
    | eapply le_term_by;eauto with imcore
    | eapply le_term_con;eauto with imcore
    | eapply le_term_var;eauto with imcore
    | eapply le_term_trans;eauto with imcore
    | eapply le_term_sym;eauto with imcore
    | eapply le_term_conv;eauto with imcore].
    rewrite in_cons; apply /orP; right; eassumption.
    rewrite in_cons; apply /orP; right; eassumption.
  }
  {
    intro les; destruct les; constructor; eauto with imcore.
  }
  {
    intro lea; destruct lea; constructor; eauto with imcore.
  }
Qed.

Hint Resolve le_sort_lang_monotonicity : imcore.
Hint Resolve le_term_lang_monotonicity : imcore.
Hint Resolve le_subst_lang_monotonicity : imcore.
Hint Resolve le_args_lang_monotonicity : imcore.

Lemma wf_sort_lang_monotonicity l c t name r
  : wf_sort l c t ->
    wf_sort ((name,r)::l) c t
with wf_term_lang_monotonicity l c e t name r
     : wf_term l c e t ->
       wf_term ((name,r)::l) c e t
with wf_args_lang_monotonicity l c al args el c' name r
     : wf_args l c al args el c'->
       wf_args ((name,r)::l) c al args el c'.
Proof using.
  {
    intro les; destruct les; eapply wf_sort_by; eauto with imcore.
    rewrite in_cons; apply /orP; auto.
  }
  {
    intro letm; destruct letm;
    [eapply wf_term_by;eauto with imcore
    | eapply wf_term_conv;eauto with imcore
    | eapply wf_term_var;eauto with imcore].
    rewrite in_cons; apply /orP; auto.
  }
  {
    intro les; destruct les; constructor; eauto with imcore.
  }
Qed.


Hint Resolve wf_sort_lang_monotonicity : imcore.
Hint Resolve wf_term_lang_monotonicity : imcore.
Hint Resolve wf_args_lang_monotonicity : imcore.

Lemma wf_ctx_lang_monotonicity l c name r
  : wf_ctx l c -> wf_ctx ((name,r)::l) c.
Proof.
  intro wfc; induction wfc; eauto with imcore.
Qed.

Hint Resolve wf_ctx_lang_monotonicity : imcore.

Lemma wf_rule_lang_monotonicity l r name r'
  : wf_rule l r -> wf_rule ((name,r')::l) r.
Proof.
  intro wfr; destruct wfr; constructor; eauto with imcore.
Qed.

Hint Resolve wf_rule_lang_monotonicity : imcore.

Lemma wf_rule_in l r name
  : wf_lang l -> (name,r) \in l -> wf_rule l r.
Proof.
  intro wfl; induction wfl.
  { rewrite in_nil; intro fls; inversion fls. }
  {
    rewrite in_cons; move /orP => [].
    {
      move /eqP => []; intros; subst; eauto with imcore.
    }
    {
      eauto with imcore.
    }
  }
Qed.

Lemma wf_ctx_sort_rule_in l c args name
  : wf_lang l -> (name,sort_rule c args) \in l -> wf_ctx l c.
Proof.
  intros wfl nin; pose (p:= wf_rule_in wfl nin); inversion p;
    auto.
Qed.
Hint Resolve wf_ctx_sort_rule_in : imcore.

Lemma wf_ctx_term_rule_in l c args t name
  : wf_lang l -> (name,term_rule c args t) \in l -> wf_ctx l c.
Proof.
  intros wfl nin; pose (p:= wf_rule_in wfl nin); inversion p;
    auto.
Qed.
Hint Resolve wf_ctx_term_rule_in : imcore.
(*TODO: specialize more cases for eauto?*)

Lemma le_sort_l_wf l c t1 t2
  : wf_lang l ->
    le_sort l c t1 t2 ->
    wf_sort l c t1
  with le_term_l_wf l c t e1 e2
       : wf_lang l ->
         le_term l c t e1 e2 ->
         wf_term l c e1 t
  with le_subst_l_wf l c c' s1 s2
       : wf_lang l ->
         le_subst l c c' s1 s2 ->
         wf_subst l c s1 c'
  with le_args_l_wf l c c' al1 al2 args el1 el2
       : wf_lang l ->
         le_args l c c' al1 al2 args el1 el2 ->
         wf_args l c al1 args el1 c'.
Proof.
  {
    intros wfl les; destruct les.
    apply wf_rule_in in H; auto; inversion H; subst; assumption.
    eapply wf_sort_subst_monotonicity; auto with imcore.
    todo: don't have ws c'
    
    apply wf_sort_by; eauto with imcore.
  }
  {
    intro les; destruct les; eauto with imcore.
  }
  {
    intro les; destruct les; eauto with imcore.
  }
  {
    intro les; destruct les; eauto with imcore.
  }
Qed.

Lemma sound_synth_le_term l p c t e1 e2
  : wf_lang l ->
    Some (t,e1,e2) = synth_le_term l p c ->
    le_term l c t e1 e2
with sound_synth_le_args l p c c' al1 al2 args el1 el2 al12 al22
     : wf_lang l ->
       wf_ctx l c' ->
       Some (el1,el2) = synth_le_args (synth_le_term l) p c c' ->
       Some al1 = get_subseq args (with_names_from c' el1) ->
       Some al2 = get_subseq args (with_names_from c' el2) ->
       al12 = map snd al1 ->
       al22 = map snd al2 ->
       le_args l c c' al12 al22 args el1 el2
with sound_synth_le_sort l p c t1 t2
     : Some (t1,t2) = synth_le_sort l (synth_le_term l) p c ->
       le_sort l c t1 t2.
Proof.
  {
    intro wfl.
    destruct p; simpl;
        repeat case_match;intros;
          repeat match goal with
          | [H : Some _ = Some _|-_] => inversion H; clear H; subst
          | [H : None = Some _|-_] => by inversion H
          | [H : Some _ = None |-_] => by inversion H
          | [H : true = ?a |-_] => symmetry in H; change (is_true a) in H
          | [H : is_true (_ == _) |-_] => move: H => /eqP H; subst
                 end; eauto with imcore.
    {
      eapply le_term_con; eauto with imcore.
      (* TODO: need monotonicity *)
      suff: wf_rule l (term_rule c0 l1 s0).
    {
      eapply le_term_subst; eauto with imcore.
        eapply le_subst_from_args.
        eapply sound_synth_le_args; eauto using get_subseq_exact.
        rewrite map_fst_with_names_from.
        erewrite <-map_fst_with_names_from.
        apply get_subseq_exact.
        eapply synth_le_args_size_r; eauto.
        eapply synth_le_args_size_l; eauto.
      }
    }
    {
      destruct p; simpl;
        repeat case_match;intros;
          repeat (match goal with
          | [H : Some _ = Some _|-_] => inversion H; clear H; subst
          | [H : None = Some _|-_] => by inversion H
          | [H : Some _ = None |-_] => by inversion H
          | [H : true = ?a |-_] => symmetry in H; change (is_true a) in H
          | [H : is_true (_ == _) |-_] => move: H => /eqP H; subst
          | [|-le_args _ [::] _ _ ?args _ _] => destruct args; simpl in *
                  end; eauto with imcore).
      apply le_args_cons_im.
      TODO: need c' all_fresh
      destruct args;
      simpl in *.
          repeat (match goal with
          | [H : Some _ = Some _|-_] => inversion H; clear H; subst
          | [H : None = Some _|-_] => by inversion H
          | [H : Some _ = None |-_] => by inversion H
          | [H : true = ?a |-_] => symmetry in H; change (is_true a) in H
          | [H : is_true (_ == _) |-_] => move: H => /eqP H; subst
          | [|-le_args _ [::] _ _ ?args _ _] => destruct args; simpl in *
                  end; eauto with imcore); simpl.
      constructor.
      {
        eapply sound_synth_le_args; eauto with imcore.
          match goal with
          | [|-le_args _ [::] _ _ ?args _ _] => destruct args; simpl in *
          | [|-le_args _ _::_ _ _ ?args _ _] => destruct args; simpl in *
          end.
      { 
        destruct args; simpl in *;
          repeat match goal with
          | [H : Some _ = Some _|-_] => inversion H; clear H; subst
          | [H : None = Some _|-_] => by inversion H
          | [H : Some _ = None |-_] => by inversion H
          | [H : true = ?a |-_] => symmetry in H; change (is_true a) in H
          | [H : is_true (_ == _) |-_] => move: H => /eqP H; subst
                 end; eauto with imcore.
      }
      {
        
        
        eapply le_term_conv.
      }
      {
        
