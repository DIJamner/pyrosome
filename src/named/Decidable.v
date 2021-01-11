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
         | _,_,_,_,_ => false (*TODO*)
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
