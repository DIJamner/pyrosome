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
  term_args_elab : ctx -> list exp -> string -> sort -> option (list exp);
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
  sort_args_elab : ctx -> list exp -> string -> option (list exp);
  (*elaborate_sort_implicits
  : forall n c name s,
      let r := named_list_lookup (sort_rule [::] [::]) l name in
      let args := get_rule_args r in
      let c' := get_rule_ctx r in
      wf_lang (nth_tail n l) ->
      (wf_sort (nth_tail n l) c (scon name s))
      <-> wf_args (nth_tail n l) c s args (sort_args_elab c s name) c'*)
  }.

Require Monad.

Section Base.

  Inductive wfness_goal : Set :=
  | wf_sort_goal : nat -> ctx -> sort -> wfness_goal
  | wf_term_goal : nat -> ctx -> exp -> sort -> wfness_goal
  | le_sort_goal : nat -> ctx -> sort -> sort -> wfness_goal
  | le_term_goal : nat -> ctx -> sort -> exp -> exp -> wfness_goal.

  Definition dec_monad (A : Set) : Set := option (list wfness_goal * A).

  Import Monad.
  
  Instance dec_monad_instance : Monad dec_monad :=
    {
    Mret _ a := Some ([::],a);
    Mbind _ _ f ma :=
      match ma with
      | Some (l,a) =>
        Option.map (fun p => (p.1++l, p.2)) (f a)
      | None => None
      end;
      Mfail _ := None
    }.
  
  Definition add_goal (g : wfness_goal) : dec_monad unit :=
    Some ([:: g],tt).

  Local Definition lift {A : Set} (e : option A) : dec_monad A :=
    match e with
    | Some e' => Mret e'
    | None => None
    end.

  Definition dm_catch_as (g:wfness_goal) (ma : dec_monad unit) : dec_monad unit :=
    match ma with
    | Some (l, tt) => Some (l,tt)
    | None => add_goal g
    end.
  
  Variable l : lang.

  Definition reify_goal (g : wfness_goal) : Prop :=
    match g with
    | wf_sort_goal n c t => wf_sort (nth_tail n l) c t
    | wf_term_goal n c e t => wf_term (nth_tail n l) c e t
    | le_sort_goal n c t1 t2 => le_sort (nth_tail n l) c t1 t2
    | le_term_goal n c t e1 e2 => le_term (nth_tail n l) c t e1 e2
    end.

  Definition reify_all_goals (l : list wfness_goal) : Prop :=
    List.Forall reify_goal l.

  Definition dm_remaining_goals (res : dec_monad unit) : Prop :=
    match res with
    | Some (l, tt) => reify_all_goals l
    | None => False
    end.
  Arguments dm_remaining_goals !res /.
    
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
  
  Definition try_le_sort n c t' t : dec_monad unit :=
    if le_sort_dec n c t' t
    then do ret tt else add_goal (le_sort_goal n c t' t).  

  Fixpoint wf_term_dec n c e t fuel : dec_monad unit :=
    dm_catch_as (wf_term_goal n c e t)
    (match e with
    | var x =>
      do t' <- lift (named_list_lookup_err c x);
         tt <- try_le_sort n c t' t;
         ret tt
    | con name s =>
      do (S fuel') <?- do ret fuel;
         (term_rule c' args t') <?- lift (named_list_lookup_err (nth_tail n l) name);
         es <- lift (term_args_elab c s name t);
         tt <- wf_sort_dec n c t'[/with_names_from c' es/] fuel';
         tt <- try_le_sort n c t'[/with_names_from c' es/] t;
         tt <- wf_args_dec n c s args es c' fuel';
         ret tt
    end)
  with wf_args_dec n c s args es c' fuel : dec_monad unit :=
         match c',es, args, s with
         | [::], [::], [::], [::] => do ret tt
         | [::], _, _, _ => Mfail
         | (name,t)::c'', [::], _, _ => Mfail
         | (name,t)::c'', e::es', [::], [::] =>
           do (S fuel') <?- do ret fuel;
              tt <- wf_term_dec n c e t[/with_names_from c'' es'/] fuel';
              tt <- wf_args_dec n c [::] [::] es' c'' fuel'; 
              ret tt
         |  (name,t)::c'', e::es', name'::args', e'::s' =>
           if name == name'
           then do (S fuel') <?- do ret fuel;
                   !e == e';
                   tt <- wf_term_dec n c e t[/with_names_from c'' es'/] fuel';
                   tt <- wf_args_dec n c s' args' es' c'' fuel';
                   ret tt
           else do (S fuel') <?- do ret fuel;
              tt <- wf_term_dec n c e t[/with_names_from c'' es'/] fuel';
              tt <- wf_args_dec n c [::] [::] es' c'' fuel'; 
              ret tt
         | _,_,_,_ => Mfail (*TODO?*)
         end
  with wf_sort_dec n c t fuel : dec_monad unit :=
  dm_catch_as (wf_sort_goal n c t)
    (do (S fuel') <?- do ret fuel;
        let (scon name s) := t;
        (sort_rule c' args) <?- lift (named_list_lookup_err (nth_tail n l) name);
        es <- lift (sort_args_elab c s name);
        tt <- wf_args_dec n c s args es c' fuel';
        ret tt).

  Arguments wf_term_dec n c !e t !fuel/.
  Arguments wf_args_dec n c !s !args !es !c' !fuel/.
  Arguments wf_sort_dec n c !t !fuel/.

  Lemma decide_wf_term n c e t fuel
    : wf_lang (nth_tail n l) ->
      wf_ctx (nth_tail n l) c ->
      wf_sort (nth_tail n l) c t ->
      dm_remaining_goals (wf_term_dec n c e t fuel) -> wf_term (nth_tail n l) c e t
  with decide_wf_args n c s args es c' fuel
       : wf_lang (nth_tail n l) ->
         wf_ctx (nth_tail n l) c ->
         wf_ctx (nth_tail n l) c' ->
         dm_remaining_goals (wf_args_dec n c s args es c' fuel) -> wf_args (nth_tail n l) c s args es c'
  with decide_wf_sort n c t fuel
       : wf_lang (nth_tail n l) ->
         wf_ctx (nth_tail n l) c ->
         dm_remaining_goals (wf_sort_dec n c t fuel) -> wf_sort (nth_tail n l) c t.
  Proof.
(* TODO    {
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
    }*)
  Admitted.

  Fixpoint wf_ctx_dec n c fuel : dec_monad unit :=
    match c with
    | [::] => do ret tt
    | (name,t)::c'=>
      do !fresh name c';
      tt <- wf_sort_dec n c' t fuel;
      tt <- wf_ctx_dec n c' fuel;
      ret tt
  end.
  Arguments wf_ctx_dec n !c fuel/.

  Lemma reify_all_goals_cat l0 l1
    : reify_all_goals (l1 ++ l0) <-> reify_all_goals l0 /\ reify_all_goals l1.
  Proof.
    unfold reify_all_goals.
    rewrite List.Forall_app.
    ltac1:(easy).
  Qed.
    
  (*TODO: move up*)
  Lemma split_remaining_goals f mtt
    : dm_remaining_goals (Mbind f mtt)
      <-> dm_remaining_goals mtt /\ dm_remaining_goals (f tt).
  Proof.
    destruct mtt;ltac1:(break).
    {
      simpl.
      remember (f tt) as mtt'.
      (destruct mtt'; ltac1:(break);
        simpl)>[ apply reify_all_goals_cat |ltac1:(easy)].
    }
    {
      ltac1:(easy).
    }
  Qed.

  Arguments Mbind : simpl never.

  Lemma decide_wf_ctx n c fuel
       : wf_lang (nth_tail n l) ->
         dm_remaining_goals (wf_ctx_dec n c fuel) -> wf_ctx (nth_tail n l) c.
  Proof.
    induction c; intros; ltac1:(break); constructor; auto;
      revert H0; simpl; repeat ltac1:(case_match); subst;
        rewrite ?split_remaining_goals;intro; ltac1:(break); eauto using decide_wf_sort;
          apply False_ind; assumption.
  Qed.
   

  Definition wf_rule_dec n r fuel : dec_monad unit :=
    match r with
    | sort_rule c args =>
      do !subseq args (map fst c);
         tt <- wf_ctx_dec n c fuel;
         ret tt
    | term_rule c args t =>
      do !subseq args (map fst c);
         tt <- wf_ctx_dec n c fuel;
         tt <- wf_sort_dec n c t fuel;
         ret tt
    | sort_le c t1 t2 =>
      do tt <- wf_ctx_dec n c fuel;
         tt <- wf_sort_dec n c t1 fuel;
         tt <- wf_sort_dec n c t2 fuel;
         ret tt
    | term_le c e1 e2 t =>
      do tt <- wf_ctx_dec n c fuel;
         tt <- wf_sort_dec n c t fuel;
         tt <- wf_term_dec n c e1 t fuel;
         tt <- wf_term_dec n c e2 t fuel;
         ret tt
    end.

  Lemma decide_wf_rule n r fuel
       : wf_lang (nth_tail n l) ->
         dm_remaining_goals (wf_rule_dec n r fuel) -> wf_rule (nth_tail n l) r.
  Proof.
    intro.
    destruct r;
    simpl; repeat ltac1:(case_match); subst;
      rewrite ?split_remaining_goals;intro; ltac1:(break); constructor;
        eauto using decide_wf_sort, decide_wf_ctx, decide_wf_term;
          apply False_ind; assumption.
  Qed.

  Fixpoint wf_lang_dec' n l fuel : dec_monad unit :=
    match l with
    | [::] => do ret tt
    | (name,r)::l' =>
      do !(fresh name l');
         tt <- wf_rule_dec n.+1 r fuel;
         tt <- wf_lang_dec' n.+1 l' fuel;
         ret tt
    end.

  Definition wf_lang_dec fuel : dec_monad unit :=
    wf_lang_dec' 0 l fuel.

  Lemma decide_wf_lang' n fuel
    : dm_remaining_goals (wf_lang_dec' n (nth_tail n l) fuel) -> wf_lang (nth_tail n l).
  Proof.
    remember (nth_tail n l) as nl.
    revert n Heqnl.
    induction nl.
    { constructor. }
    {
      intros n ntheq;ltac1:(break); simpl in *.
      simpl; repeat ltac1:(case_match); subst;
      rewrite ?split_remaining_goals;intro; ltac1:(break); constructor;
        eauto using decide_wf_rule;    
          try (solve[apply False_ind; assumption]).
      {
        eapply (IHnl (S n)).
        ltac1:(simple eapply nth_tail_cons_eq); eauto.
        assumption.
      }
      {
        ltac1:(simple apply nth_tail_cons_eq in ntheq).
        rewrite ntheq.
        eapply decide_wf_rule; eauto.
        rewrite <-ntheq.
        eauto.
      }
    }
  Qed.

  Lemma decide_wf_lang fuel : dm_remaining_goals (wf_lang_dec fuel) -> wf_lang l.
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

  (*TODO: not true in general!*)
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


(*
(* Tools for proof debugging *)
Module InteractiveTactics.
  Lemma unfold_wf_term_dec l lr n c name s t fuel'
  : wf_term_dec lr  n c (con name s) t (S fuel')
    = match named_list_lookup_err (nth_tail n l) name with
      | Some (term_rule c' args t') =>
        let es := @term_args_elab l lr c s name t in
        (wf_sort_dec lr n c t'[/with_names_from c' es/] fuel') &&
        (le_sort_dec n c t'[/with_names_from c' es/] t) &&
        (wf_args_dec lr n c s args es c' fuel')
      | _ => false
      end.
  Proof.
    reflexivity.
  Qed.

  Lemma unfold_wf_args_dec l (lr : LangRecognize l) n c s args es c' fuel'
    : wf_args_dec lr n c s args es c' (S fuel') =
      match c',es, args, s with
      | [::], [::], [::], [::] => true
      | [::], _, _, _ => false
      | (name,t)::c'', [::], _, _ => false
      | (name,t)::c'', e::es', [::], [::] =>
        (wf_term_dec lr n c e t[/with_names_from c'' es'/] fuel') &&
        (wf_args_dec lr n c [::] [::] es' c'' fuel')
      | (name,t)::c'', e::es', name'::args', e'::s' =>
        if name == name'
        then (e == e') &&
             (wf_term_dec lr n c e t[/with_names_from c'' es'/] fuel') &&
             (wf_args_dec lr n c s' args' es' c'' fuel')
        else (wf_term_dec lr n c e t[/with_names_from c'' es'/] fuel') &&
             (wf_args_dec lr n c s args es' c'' fuel')
      | _,_,_,_ => false (*TODO?*)
      end.
  Proof.
    reflexivity.
  Qed.

  Lemma unfold_wf_sort_dec l lr n c t fuel'
    :  wf_sort_dec lr n c t (S fuel') =
       match t with
       | scon name s =>
         match named_list_lookup_err (nth_tail n l) name with
         | Some (sort_rule c' args) =>
           let es := sort_args_elab (l:=l) c s name in
           (wf_args_dec lr n c s args es c' fuel')
         | _ => false
         end
       end.
  Proof.
    reflexivity.
  Qed.


  (*TODO: may need lang name(s) passed in for cbv*)
  Ltac2 unfold_wf_term_dec () :=
    rewrite unfold_wf_term_dec; 
    cbv [nth_tail named_list_lookup_err
              cat fst snd
              String.eqb Ascii.eqb Bool.eqb].


  (*TODO: may need lang name(s) passed in for cbv*)
  Ltac2 unfold_wf_sort_dec () :=
    rewrite unfold_wf_sort_dec;
    cbv [nth_tail named_list_lookup_err
              cat fst snd
              String.eqb Ascii.eqb Bool.eqb].

  Ltac2 break_dec_goal () :=
    ltac1:(apply /andP); split; try (solve[vm_compute; reflexivity]).

End InteractiveTactics.
*)
