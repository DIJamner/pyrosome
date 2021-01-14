Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


From Ltac2 Require Import Ltac2.
From Utils Require Import Utils.
From Named Require Import Exp Rule ARule Tactics.
From Named Require ICore.
Import ICore.IndependentJudgment.
Import Exp.Notations ARule.Notations. (* TODO: Rule.Notations.*)
Require Import String.

Require Import Named.Recognizers.

Set Default Proof Mode "Ltac2".


(*TODO: weaken to recognize for now? eventually want reflect?*)
Class LangRecognize (l : lang) : Type :=
  {
  le_sort_dec : nat -> ctx -> sort -> sort -> bool;
  decide_le_sort : forall n c t1 t2,
      wf_lang (nth_tail n l) ->
      wf_sort (nth_tail n l) c t1 ->
      wf_sort (nth_tail n l) c t2 ->
      (le_sort_dec n c t1 t2) -> (le_sort (nth_tail n l) c t1 t2);
  term_args_elab : ctx -> list exp -> string -> sort -> list exp;
  (* only needed for proof of other direction *)
  (*elaborate_term_implicits
  : forall n c name s t,
      let r := named_list_lookup (sort_rule [::] [::]) l name in
      let args := get_rule_args r in
      let c' := get_rule_ctx r in
      let t' := get_rule_sort r in
      wf_lang (nth_tail n l) ->
      (wf_term (nth_tail n l) c (con name s) t)
      <-> wf_args (nth_tail n l) c s args (term_args_elab c s name t) c';*)
  sort_args_elab : ctx -> list exp -> string -> list exp;
  (*elaborate_sort_implicits
  : forall n c name s,
      let r := named_list_lookup (sort_rule [::] [::]) l name in
      let args := get_rule_args r in
      let c' := get_rule_ctx r in
      wf_lang (nth_tail n l) ->
      (wf_sort (nth_tail n l) c (scon name s))
      <-> wf_args (nth_tail n l) c s args (sort_args_elab c s name) c'*)
  }.

Section Base.

  Variable l : lang.
  Context (langrec : LangRecognize l).


  (* TODO: not well-founded b/c of implicit arguments! need a rule about implicits depth.
     For now I will only reason about recognization.
   *)
  (*Parameter implicits_size_cap : nat.
  
  

  Fixpoint depth (e : exp) : nat :=
    match e with
    | con _ s => (foldr max 0 (map depth s)).+2
    | var _ => 0
    end.
  Definition args_depth s : nat := (foldr max 0 (map depth s)).+1.
   *)     
  
  Fixpoint wf_term_dec n c e t fuel : bool :=
    match fuel, e with
    | 0,_ => false
    | S fuel', var x =>
      match named_list_lookup_err c x with
      | Some t' => le_sort_dec n c t' t
      | None => false
      end
    | S fuel', con name s =>
      match named_list_lookup_err (nth_tail n l) name with
      | Some (term_rule c' args t') =>
        let es := term_args_elab c s name t in
        (wf_sort_dec n c t'[/with_names_from c' es/] fuel') &&
        (le_sort_dec n c t'[/with_names_from c' es/] t) &&
        (wf_args_dec n c s args es c' fuel')
      | _ => false
      end
    end
  with wf_args_dec n c s args es c' fuel : bool :=
         match fuel, c',es, args, s with
         | 0,_,_,_,_=> false
         | S fuel', [::], [::], [::], [::] => true
         | S fuel', [::], _, _, _ => false
         | S fuel', (name,t)::c'', [::], _, _ => false
         | S fuel', (name,t)::c'', e::es', [::], [::] =>
           (wf_term_dec n c e t[/with_names_from c'' es'/] fuel') &&
           (wf_args_dec n c [::] [::] es' c'' fuel')
         | S fuel', (name,t)::c'', e::es', name'::args', e'::s' =>
           if name == name'
           then (e == e') &&
                (wf_term_dec n c e t[/with_names_from c'' es'/] fuel') &&
                (wf_args_dec n c s' args' es' c'' fuel')
           else (wf_term_dec n c e t[/with_names_from c'' es'/] fuel') &&
                (wf_args_dec n c s args es' c'' fuel')
         | _,_,_,_,_ => false (*TODO?*)
         end
  with wf_sort_dec n c t fuel : bool :=
    match fuel, t with
    | 0,_ => false
    | S fuel', scon name s =>
      match named_list_lookup_err (nth_tail n l) name with
      | Some (sort_rule c' args) =>
        let es := sort_args_elab c s name in
        (wf_args_dec n c s args es c' fuel')
      | _ => false
      end
    end.

  Arguments wf_term_dec n c !e t !fuel/.
  Arguments wf_args_dec n c !s !args !es !c' !fuel/.
  Arguments wf_sort_dec n c !t !fuel/.

  Lemma decide_wf_term n c e t fuel
    : wf_lang (nth_tail n l) ->
      wf_ctx (nth_tail n l) c ->
      wf_sort (nth_tail n l) c t ->
      wf_term_dec n c e t fuel -> wf_term (nth_tail n l) c e t
  with decide_wf_args n c s args es c' fuel
       : wf_lang (nth_tail n l) ->
         wf_ctx (nth_tail n l) c ->
         wf_ctx (nth_tail n l) c' ->
         wf_args_dec n c s args es c' fuel -> wf_args (nth_tail n l) c s args es c'
  with decide_wf_sort n c t fuel
       : wf_lang (nth_tail n l) ->
         wf_ctx (nth_tail n l) c ->
         wf_sort_dec n c t fuel -> wf_sort (nth_tail n l) c t.
  Proof using Type.
    {
      intros wfl wfc wfs.
      destruct fuel> [intro fls; inversion fls|].
      destruct e; simpl;
        repeat (ltac1:(case_match)); try (solve[intro fls; inversion fls]).
      {
        intros.
        eapply wf_term_conv>[| |apply decide_le_sort in H; eauto].
        admit.
        constructor.
        ltac1:(simple apply (@named_list_lookup_err_in)).
        symmetry; eauto.
        admit.
      }
      {
        repeat ltac1:(move => /andP []).
        intros.        
        eapply wf_term_conv>[| |apply decide_le_sort in b; eauto]; auto.
        (*wf sort subst*)admit.
        eapply wf_term_by; simpl; auto.
        ltac1:(simple apply (@named_list_lookup_err_in)).
        symmetry; eauto.
        apply decide_wf_args in b0; auto.
        (* wf_rule in *)admit.
      }
    }
    {
      intros wfl wfc wfc'.
      destruct fuel> [intro fls; inversion fls|].
      destruct c'; destruct es; ltac1:(break);
        destruct args; destruct s; ltac1:(break);simpl;
          try (solve[intro fls; inversion fls]).
      { constructor. }
      {        
        ltac1:(move => /andP []).
        inversion wfc'; subst.
        constructor; eauto.
        eapply decide_wf_term; eauto.
        (* sort subst pres. wf*) admit.
      }
      {
        remember (s0==s2) as eqs; destruct eqs.
        {
          symmetry in Heqeqs.
          ltac1:(move: Heqeqs => /eqP ?); subst.
          inversion wfc'; subst.
          repeat ltac1:(move => /andP []).
          ltac1:(move => /eqP ?); subst.
          constructor; eauto.
          apply decide_wf_term in b; eauto.
          (* sort subst pres. wf*) admit.
        }
        {
          inversion wfc'; subst.
          repeat ltac1:(move => /andP []).
          intros.
          apply wf_args_cons_im; eauto.
          apply decide_wf_term in a; eauto.
          (* sort subst pres. wf*) admit.
        }
      }
    }
    {
      intros wfl wfc.
      destruct fuel> [intro fls; inversion fls|].
      destruct t; simpl;
        repeat (ltac1:(case_match)); try (solve[intro fls; inversion fls]).
      repeat ltac1:(move => /andP []).
      ltac1:(move => /decide_wf_args wfa).
      eapply wf_sort_by; simpl; auto.
      ltac1:(simple apply (@named_list_lookup_err_in)).
      symmetry; eauto.
      apply wfa; auto.
      (* from wf lang *)admit.
    }
  Admitted.

  Fixpoint wf_ctx_dec n c fuel : bool :=
    match c with
    | [::] => true
    | (name,t)::c'=>
      (fresh name c') &&
      (wf_sort_dec n c' t fuel) &&
      (wf_ctx_dec n c' fuel)
    end.

  Arguments wf_ctx_dec n !c fuel/.

  Lemma decide_wf_ctx n c fuel
       : wf_lang (nth_tail n l) ->
         wf_ctx_dec n c fuel -> wf_ctx (nth_tail n l) c.
  Proof.
    induction c; intros; ltac1:(break); simpl in *; constructor; auto;
    revert H0;
    repeat ltac1:(move => /andP []);
    intros; auto.
    eapply decide_wf_sort; eauto.
  Qed.    

  Definition wf_rule_dec n r fuel : bool :=
    match r with
    | sort_rule c args =>
      (subseq args (map fst c)) &&
      (wf_ctx_dec n c fuel)
    | term_rule c args t =>
      (subseq args (map fst c)) &&
      (wf_ctx_dec n c fuel) &&
      (wf_sort_dec n c t fuel)
    | sort_le c t1 t2 =>
      (wf_ctx_dec n c fuel) &&
      (wf_sort_dec n c t1 fuel) &&
      (wf_sort_dec n c t2 fuel)
    | term_le c e1 e2 t =>
      (wf_ctx_dec n c fuel) &&
      (wf_term_dec n c e1 t fuel) &&
      (wf_term_dec n c e2 t fuel) &&
      (wf_sort_dec n c t fuel)
    end.

  Lemma decide_wf_rule n r fuel
       : wf_lang (nth_tail n l) ->
         wf_rule_dec n r fuel -> wf_rule (nth_tail n l) r.
  Proof.
    intro.
    destruct r;
    repeat ltac1:(move => /andP []);
    intros; constructor; eauto using decide_wf_ctx, decide_wf_sort, decide_wf_term.
  Qed.

  Fixpoint wf_lang_dec' n l fuel : bool :=
    match l with
    | [::] => true
    | (name,r)::l' =>
      (fresh name l') &&
      (wf_rule_dec n.+1 r fuel) &&
      (wf_lang_dec' n.+1 l' fuel)
    end.

  Definition wf_lang_dec fuel : bool :=
    wf_lang_dec' 0 l fuel.

(*
Lemma decide_wf_lang_succ n name r fuel
  : wf_lang_dec' n.+1 (nth_tail n.+1 l) fuel ->
    fresh name (nth_tail n.+1 l) ->
    wf_rule_dec n r fuel ->
    wf_lang_dec' n (nth_tail n l) fuel.
Proof.
  intros.
  destruct l.
  { destruct n; simpl; auto. }
  {
    destruct n; simpl; ltac1:(break); auto.
    {
      ltac1:(break_goal); auto.
      unfold nth_tail in H.
      repeat ltac1:(move => /andP []).      
    simpl.
  *)

  Lemma decide_wf_lang' n fuel
    : wf_lang_dec' n (nth_tail n l) fuel -> wf_lang (nth_tail n l).
  Proof.
    remember (nth_tail n l) as nl.
    revert n Heqnl.
    induction nl.
    { constructor. }
    {
      intros; ltac1:(break); simpl in *.
      revert H;
        repeat ltac1:(move => /andP []);
        intros.
      constructor; auto.
      {
        eapply (IHnl (S n)).
        ltac1:(simple eapply nth_tail_cons_eq); eauto.
        assumption.
      }
      {
        ltac1:(simple apply nth_tail_cons_eq in Heqnl).
        rewrite Heqnl.
        eapply decide_wf_rule; eauto.
        rewrite <-Heqnl.
        eauto.
      }
    }
  Qed.

  Lemma decide_wf_lang fuel : wf_lang_dec fuel -> wf_lang l.
  Proof.
    unfold wf_lang_dec.
    apply decide_wf_lang'.
  Qed.


End Base.



(*TODO: prove, put in right place *)
Parameter le_subst_refl
     : forall (l : lang) (c : ctx) (s : subst) (c' : ctx),
    map fst s = map fst c' -> le_subst l c c' s s.

Section SingleStep.
(*TODO: connect to matches?*)
(* Variant sort_redex_steps_1 (l : lang) t1 t2 name: Prop :=
  sort_steps_1 : forall c t1' t2' s,
    (name, sort_le c t1' t2') \in l ->
    t1 = t1'[/s/] ->
    t2 = t2'[/s/] ->
    map fst s = map fst c ->
    sort_redex_steps_1 l t1 t2 name. *)



Inductive term_steps_1 (l : lang) name : sort -> exp -> exp -> Prop :=
| term_redex_steps_1 : forall c' e1' e2' t' s,
    (name, term_le c' e1' e2' t') \in l ->
    map fst s = map fst c' ->
    term_steps_1 l name t'[/s/] e1'[/s/] e2'[/s/]
| term_eval_ctx_steps_1 : forall ename c' t' args1 args2 args s1 s2,
    (*TODO: needed?*)
    (ename, term_rule c' args t') \in l ->
    args_steps_1 l name c' args1 args2 args s1 s2 ->
    term_steps_1 l name t'[/with_names_from c' s2/] (con ename args1) (con ename args2)
with args_steps_1 (l:lang) name : ctx -> list exp -> list exp -> list string -> list exp -> list exp -> Prop :=
  (* TODO: have an implicit one? prob not necessary *)
| fst_arg_steps_1 : forall ename e1 e2 t args args' s c',
    term_steps_1 l name t[/with_names_from c' s /] e1 e2 ->
    args_steps_1 l name ((ename,t)::c') (e1::args') (e2::args') (ename::args) (e1::s) (e2::s)
| rst_arg_steps_1_ex : forall ename e t args1' args2' c' args s1 s2,
    args_steps_1 l name c' args1' args2' args s1 s2 ->
    args_steps_1 l name ((ename,t)::c') (e::args1') (e::args2') (ename::args) (e::s1) (e::s2)
| rst_arg_steps_1_im : forall ename e t args1' args2' c' args s1 s2,
    args_steps_1 l name c' args1' args2' args s1 s2 ->
    args_steps_1 l name ((ename,t)::c') (args1') (args2') (args) (e::s1) (e::s2).

Lemma term_steps_1_le l name c t e1 e2
  : term_steps_1 l name t e1 e2 -> le_term l c t e1 e2
with args_steps_1_le l name c c' s1 s2 args es1 es2
     : args_steps_1 l name c' s1 s2 args es1 es2 ->
       le_args l c c' s1 s2 args es1 es2.
Proof.
  {
    intro ts; inversion ts; subst.
    eapply le_term_subst.
    { eapply le_subst_refl; eauto. }
    {
      ltac1:(simple eapply (le_term_by (name:=name))); auto.
    }
    {
      (* TODO: need congruence *)
      eapply args_steps_1_le in H0.
      admit.
    }
  }
  {
    intro argss; (inversion argss; subst)>
                 [eapply le_args_cons_ex
                 |eapply le_args_cons_ex
                 |eapply le_args_cons_im]; eauto.
    { (*TODO: reflexivity*) admit. }
    { apply le_term_refl. }
    { apply le_term_refl. }
  }
  Unshelve.
  exact c.
Admitted.

Variant sort_steps_1 (l : lang) name : sort -> sort -> Prop :=
| sort_redex_steps_1 : forall c t1 t2 s,
    (name, sort_le c t1 t2) \in l ->
    map fst s = map fst c ->
    sort_steps_1 l name t1[/s/] t2[/s/]
| sort_eval_ctx_steps_1 : forall sname args1 args2 s1 s2 c' args,
    (*TODO: needed?*)
    (sname, sort_rule c' args) \in l ->
    args_steps_1 l name c' args1 args2 args s1 s2 ->
    sort_steps_1 l name (scon sname args1) (scon sname args2).

Lemma sort_steps_1_le l name c t1 t2
  : sort_steps_1 l name t1 t2 -> le_sort l c t1 t2.
Proof.
  {
    intro ts; inversion ts; subst.
    eapply le_sort_subst.
    { eapply le_subst_refl; eauto. }
    {
      ltac1:(simple eapply (le_sort_by (name:=name))); auto.
    }
    {
      (* TODO: need congruence *)
      eapply args_steps_1_le in H0.
      admit.
    }
  }
Admitted.


End SingleStep.


Require Import Matches.

Section ParStep.

  
  (* 0 or more parallel steps (involving disjoint parts of the AST) *)
  Inductive term_steps_par (l : lang) : sort -> exp -> exp -> Prop :=
  | term_redex_steps_par : forall name c' e1' e2' t' s,
      (name, term_le c' e1' e2' t') \in l ->
      map fst s = map fst c' ->
      term_steps_par l t'[/s/] e1'[/s/] e2'[/s/]
  | term_eval_ctx_steps_par : forall ename c' t' args1 args2 args s1 s2,
      args_steps_par l c' args1 args2 args s1 s2 ->
      term_steps_par l t'[/with_names_from c' s2/] (con ename args1) (con ename args2)
  with args_steps_par (l:lang) : ctx -> list exp -> list exp -> list string -> list exp -> list exp -> Prop :=
  | args_steps_par_nil : args_steps_par l [::] [::] [::] [::] [::] [::]
  (* TODO: have an implicit one? prob not necessary *)
  | fst_arg_steps_par : forall ename e1 e2 t args args1' args2' s1 s2 c',
      term_steps_par l t[/with_names_from c' s2 /] e1 e2 ->
      args_steps_par l c' args1' args2' args s1 s2 ->
      args_steps_par l ((ename,t)::c') (e1::args1') (e2::args2') (ename::args) (e1::s1) (e2::s2)
  | rst_arg_steps_par_ex : forall ename e t args1' args2' c' args s1 s2,
      args_steps_par l c' args1' args2' args s1 s2 ->
      args_steps_par l ((ename,t)::c') (e::args1') (e::args2') (ename::args) (e::s1) (e::s2)
  | rst_arg_steps_par_im : forall ename e t args1' args2' c' args s1 s2,
      args_steps_par l c' args1' args2' args s1 s2 ->
      args_steps_par l ((ename,t)::c') (args1') (args2') (args) (e::s1) (e::s2).

  
  Lemma term_steps_par_le l c t e1 e2
    : term_steps_par l t e1 e2 -> le_term l c t e1 e2
  with args_steps_par_le l c c' s1 s2 args es1 es2
       : args_steps_par l c' s1 s2 args es1 es2 ->
         le_args l c c' s1 s2 args es1 es2.
  Proof.
    {
      intro ts; inversion ts; subst.
      eapply le_term_subst.
      { eapply le_subst_refl; eauto. }
      {
        ltac1:(simple eapply (le_term_by (name:=name))); auto.
      }
      {
        (* TODO: need congruence *)
        eapply args_steps_par_le in H.
        admit.
      }
    }
    {
      intro argss; (inversion argss; subst)>
                   [apply le_args_nil
                   |eapply le_args_cons_ex
                   |eapply le_args_cons_ex
                   |eapply le_args_cons_im]; eauto.
      { apply le_term_refl. }
      { apply le_term_refl. }
    }
    Unshelve.
    exact c.
  Admitted.

  
  Variant sort_steps_par (l : lang) : sort -> sort -> Prop :=
  | sort_redex_steps_par : forall name c t1 t2 s,
      (name, sort_le c t1 t2) \in l ->
      map fst s = map fst c ->
      sort_steps_par l t1[/s/] t2[/s/]
  | sort_eval_ctx_steps_par : forall sname args1 args2 s1 s2 c' args,
      args_steps_par l c' args1 args2 args s1 s2 ->
      sort_steps_par l (scon sname args1) (scon sname args2).

  Lemma sort_steps_par_le l c t1 t2
    : sort_steps_par l t1 t2 -> le_sort l c t1 t2.
  Proof.
    {
      intro ts; inversion ts; subst.
      eapply le_sort_subst.
      { eapply le_subst_refl; eauto. }
      {
        ltac1:(simple eapply (le_sort_by (name:=name))); auto.
      }
      {
        (* TODO: need congruence *)
        eapply args_steps_par_le in H.
        admit.
      }
    }
  Admitted.

  
  Inductive sort_steps_star (l :lang) : sort -> sort -> Prop :=
  | sort_steps_refl : forall t, sort_steps_star l t t
  | sort_steps_next : forall t1 t2 t3,
      sort_steps_par l t1 t2 ->
      sort_steps_star l t2 t3 ->
      sort_steps_star l t1 t3.

  
  
  Lemma sort_steps_star_le l c t1 t2
    : sort_steps_star l t1 t2 -> le_sort l c t1 t2.
  Proof.
    intro sss; induction sss; eauto using le_sort_refl, le_sort_trans, sort_steps_par_le.
  Qed.

  (*TODO: the other direction probably holds too; might be useful? *)
  
  Import OptionMonad.
  Fixpoint term_step_redex (l : lang) (e : exp) : option exp :=
    match l with
    | [::] => None
    | (_,term_le c e1 e2 t)::l' =>
      (*TODO: check that rule is executable, i.e. FV(e1) >= FV(e2)*)
      match term_step_redex l' e with
      | Some t' => Some t'
      | None => do s <- matches_unordered e e1;
                ret e2[/s/]
      end
    | _::l' => term_step_redex l' e
    end.

  Fixpoint sort_step_redex (l : lang) (t : sort) : option sort :=
    match l with
    | [::] => None
    | (_,sort_le c t1 t2)::l' =>
      (*TODO: check that rule is executable, i.e. FV(t1) >= FV(t2)*)
      match sort_step_redex l' t with
      | Some t' => Some t'
      | None => do s <- matches_unordered_sort t t1;
                ret t2[/s/]
      end
    | _::l' => sort_step_redex l' t
    end.

  (* TODO: define as option or iterate to a fixed point? *)
  Section InnerLoop.
    Context (term_par_step : forall (l : lang) (e : exp), option exp).
    Fixpoint args_par_step l s {struct s} : option (list exp) :=
         match s with
         | [::] => None
         | e::s' =>
           match term_par_step l e, args_par_step l s' with
           | Some e', Some s'' => Some (e'::s'')
           | Some e', None => Some (e'::s')
           | None, Some s'' => Some (e::s'')
           | None, None => None
           end
         end.
  End InnerLoop.

  Fixpoint term_par_step (l : lang) (e : exp) {struct e} : option exp :=
    match term_step_redex l e, e with
    | Some e',_ => Some e'
    | None, var _ => None
    | None, con name s =>
      do s' <- args_par_step term_par_step l s;
      ret (con name s')
    end.
  
  Definition sort_par_step (l : lang) (t:sort) : option sort :=
    match sort_step_redex l t, t with
    | Some e',_ => Some e'
    | None, scon name s =>
      do s' <- args_par_step term_par_step l s;
      ret (scon name s')
    end.

  Fixpoint term_par_step_n (l : lang) (e : exp) (fuel : nat) : exp :=
    match fuel, term_par_step l e with
    | 0,_ => e
    | S _, None => e
    | S fuel', Some e' => term_par_step_n l e' fuel'
    end.
  
  Fixpoint sort_par_step_n (l : lang) (t : sort) (fuel : nat) : sort :=
    match fuel, sort_par_step l t with
    | 0,_ => t
    | S _, None => t
    | S fuel', Some t' => sort_par_step_n l t' fuel'
    end.

  Lemma sort_par_step_related
    : forall l t t', sort_par_step l t = Some t' -> sort_steps_par l t t'.
  Admitted.

  Lemma sort_par_step_n_related l t fuel : sort_steps_star l t (sort_par_step_n l t fuel).
  Proof.
    revert t.
    induction fuel.
    { cbn; apply sort_steps_refl. }
    {
      intro t.
      cbn.
      ltac1:(case_match); eauto using sort_steps_refl.
      symmetry in HeqH.
      eapply sort_par_step_related in HeqH.
      eapply sort_steps_next; eauto.
    }
  Qed.

  Lemma sort_par_step_n_le l c t fuel
    : le_sort l c t (sort_par_step_n l t fuel).
  Proof.
    auto using sort_par_step_n_related, sort_steps_star_le .
  Qed.

  Definition generic_sort_dec_fuel (fuel : nat) (l : lang)
             (n : nat) (c:ctx) t1 t2 : bool :=
    let l' := nth_tail n l in
    let t1' := sort_par_step_n l' t1 fuel in
    let t2' := sort_par_step_n l' t2 fuel in
    t1' == t2'.
  
  Lemma generic_decide_le_sort (fuel : nat) (l : lang)
    : forall n c t1 t2,
      wf_lang (nth_tail n l) ->
      wf_sort (nth_tail n l) c t1 ->
      wf_sort (nth_tail n l) c t2 ->
      (generic_sort_dec_fuel fuel l n c t1 t2) -> (le_sort (nth_tail n l) c t1 t2).
  Proof.
    unfold generic_sort_dec_fuel.
    intros n c t1 t2 _ _ _.
    ltac1:(move /eqP).
    intro speq.
    match! goal with
      [ speq : ?a = ?b|- le_sort ?l ?c _ _] =>
      assert (le_sort $l $c $a $b)>[rewrite speq; apply le_sort_refl|]
    end.
    eauto using le_sort_trans, sort_par_step_n_le, le_sort_sym, le_sort_refl.
  Qed.
  
End ParStep.
