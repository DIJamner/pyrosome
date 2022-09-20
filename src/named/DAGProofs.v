Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import NArith List.
Import ListNotations.
Open Scope list.

Require Import Tries.Canonical.
Import PTree.

From Utils Require Import Utils Monad.
From Named Require Import Core.
Import Core.Notations.

Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
          {V_default : WithDefault V}.

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).
  
  Notation eq_subst l :=
    (eq_subst (Model:= core_model l)).
  Notation eq_args l :=
    (eq_args (Model:= core_model l)).
  Notation wf_subst l :=
    (wf_subst (Model:= core_model l)).
  Notation wf_args l :=
    (wf_args (Model:= core_model l)).
  Notation wf_ctx l :=
    (wf_ctx (Model:= core_model l)).

  Variant node : Type :=
    (* variable name *)
    | tn_var : V -> node
    (* Rule label, list of subterms*)
    | tn_con : V -> list positive -> node
    | tn_trans : positive -> positive -> node
    | tn_sym : positive -> node
    | tn_conv : positive -> positive -> node
    (* sort variants *)
    | sn_con : V -> list positive -> node
    | sn_trans : positive -> positive -> node
    | sn_sym : positive -> node.

  (* We assume that the head is the root by default.
     Invariant: all indices of the head are < length of the tail
   *)

  Definition pf := list node.

  Variant node_result :=
    | term_eq_result : term -> term -> sort ->  node_result
    | sort_eq_result : sort -> sort -> node_result.

  (*TODO: backport these to core.v. Copied from TreeProofs.v*)
    
    Local Lemma term_con_congruence l c t name s1 s2 c' args t'
      : In (name, term_rule c' args t') l ->
        t = t'[/with_names_from c' s2/] ->
        wf_lang l ->
        eq_args l c c' s1 s2 ->
        eq_term l c t (con name s1) (con name s2).
    Proof.
      intros.
      assert (wf_ctx l c') by with_rule_in_wf_crush.
      rewrite <- (wf_con_id_args_subst c' s1);[| basic_core_crush..].
      rewrite <- (wf_con_id_args_subst c' s2);[|basic_core_crush..].
      subst.
      change (con ?n ?args[/?s/]) with (con n args)[/s/].
      eapply eq_term_subst; eauto.
      {
        apply eq_args_implies_eq_subst; eauto.
      }
      {
        constructor.
        replace t' with t'[/id_subst c'/].
        - eapply wf_term_by; basic_core_crush.
        - basic_core_crush.
      }
    Qed.

    
    Local Lemma sort_con_congruence l c name s1 s2 c' args
      : In (name, sort_rule c' args) l ->
        wf_lang l ->
        eq_args l c c' s1 s2 ->
        eq_sort l c (scon name s1) (scon name s2).
    Proof.
      intros.
      assert (wf_ctx l c') by with_rule_in_wf_crush.
      rewrite <- (wf_con_id_args_subst c' s1);[| basic_core_crush..].
      rewrite <- (wf_con_id_args_subst c' s2);[|basic_core_crush..].
      subst.
      change (scon ?n ?args[/?s/]) with (scon n args)[/s/].
      eapply eq_sort_subst; eauto.
      { apply eq_args_implies_eq_subst; eauto. }
      { constructor.
        eapply wf_sort_by; basic_core_crush.
      }
    Qed.
  
  Section WithLang.

    Context (l : lang).
    (*TODO: change section name?*)
    Context (c : ctx).
    Context (wfl : wf_lang l).

    
     (*TOOD: replace case_match with this? Copied twice already*)
     Ltac case_match' :=
       try lazymatch goal with
           [ H :  context [ match ?e with
                            | _ => _
                            end] |- _ ] => revert H
         end;
       case_match.
    
  Section Inner.

    Context (proof_result : tree node_result).
    
    Fixpoint check_args_proof (args : list positive) (c' : ctx) :=
      match args, c' with
      | [], [] => Some ([],[])
      | p::args, (_,t)::c'=>
          @! let (lhs, rhs) <- check_args_proof args c' in
            let (term_eq_result e1 e2 t') <?- get p proof_result in
            (*TODO: use Eqb instance*)
            let ! sort_eq_dec t[/with_names_from c' rhs/] t' in
            ret (e1::lhs, e2::rhs)
      | _,_=> None
      end.

     Definition check_node (n : node) : option node_result :=
      match n with
      | tn_var n =>
          @! let t <- named_list_lookup_err c n in
             ret (term_eq_result (var n) (var n) t)
      | tn_con n s =>
          @! let r <- named_list_lookup_err l n in
             match r with
             | term_rule c' _ t =>
                 @! let (lhs, rhs) <- check_args_proof s c' in
                   ret (term_eq_result (con n lhs) (con n rhs)
                          t[/with_names_from c' rhs/])
             | term_eq_rule c' e1 e2 t =>
                 @! let (lhs, rhs) <- check_args_proof s c' in
                    let lsub := with_names_from c' lhs in
                    let rsub := with_names_from c' rhs in
                    ret (term_eq_result e1[/lsub/] e2[/rsub/] t[/rsub/])
             | _ => None
             end
      | tn_trans p0 p1 =>
          @! let (term_eq_result e1 e2 t) <?- get p0 proof_result in
             let (term_eq_result e1' e2' t') <?- get p1 proof_result in
             let ! sort_eq_dec t t' in
             let ! term_eq_dec e2 e1' in
             ret (term_eq_result e1 e2' t)
      | tn_sym p =>
          @! let (term_eq_result e1 e2 t) <?- get p proof_result in
             ret (term_eq_result e2 e1 t)
      | tn_conv p0 p1 =>
          @! let (sort_eq_result t1 t2) <?- get p0 proof_result in
             let (term_eq_result e1 e2 t) <?- get p1 proof_result in
             let ! sort_eq_dec t t1 in
             ret (term_eq_result e1 e2 t2)
                 
      | sn_con n s =>
          @! let r <- named_list_lookup_err l n in
             match r with
             | sort_rule c' _ =>
                 @! let (lhs, rhs) <- check_args_proof s c' in
                    ret (sort_eq_result (scon n lhs) (scon n rhs))
             | sort_eq_rule c' t1 t2 =>
                 @! let (lhs, rhs) <- check_args_proof s c' in
                    let lsub := with_names_from c' lhs in
                    let rsub := with_names_from c' rhs in
                    ret (sort_eq_result t1[/lsub/] t2[/rsub/])
             | _ => None
             end
      | sn_trans p0 p1 =>
          @! let (sort_eq_result t1 t2) <?- get p0 proof_result in
             let (sort_eq_result t1' t2') <?- get p1 proof_result in
             let ! sort_eq_dec t2 t1' in
             ret (sort_eq_result t1 t2')
      | sn_sym p =>
          @! let (sort_eq_result t1 t2) <?- get p proof_result in
             ret (sort_eq_result t2 t1)
      end.

     
     Definition node_result_sound res :=
       match res with
       | term_eq_result e1 e2 t => eq_term l c t e1 e2
       | sort_eq_result t1 t2 => eq_sort l c t1 t2
       end.

     (* TODO: move somewhere? *)
     Definition tree_all {A} (P : A -> Prop) t :=
       forall n a, get n t = Some a -> P a.

     Context (history_sound : tree_all node_result_sound proof_result).

     
     Lemma check_args_proof_sound args c' a1 a2
       : check_args_proof args c' = Some (a1,a2) ->
         eq_args l c c' a1 a2.
     Proof.
       revert c' a1 a2.
       induction args; destruct c';
         basic_goal_prep;
         try congruence;
         repeat case_match';
         basic_goal_prep;
         try congruence;
         repeat lazymatch goal with
           | [H : (_,_) = ( _,_) |- _ ] => safe_invert H
           | [H : Some _ = Some _ |- _ ] => safe_invert H
          end.
       - constructor.
       - constructor; eauto.
         symmetry in HeqH1.
         eapply history_sound in HeqH1.
         exact HeqH1.
       - safe_invert H.
       - safe_invert H.
     Qed.
     
     Lemma check_node_sound n res
       : check_node n = Some res ->
         node_result_sound res.
     Proof.
       destruct n;
        basic_goal_prep;
        (*weed out trivial goals for efficiency*)
        try congruence;
         repeat case_match';
        basic_goal_prep;
        try congruence;
        repeat lazymatch goal with
        | [H : default = Some _ |- _ ] => safe_invert H
        | [H : Some _ = Some _ |- _ ] => safe_invert H
          end;
         basic_goal_prep;
           repeat lazymatch goal with
           | [H : Some (term_eq_result _ _ _) = _,
                 hist : tree_all node_result_sound _ |- _] =>
               symmetry in H;
               eapply hist in H
           | [H : Some (sort_eq_result _ _) = _,
                 hist : tree_all node_result_sound _ |- _] =>
               symmetry in H;
               eapply hist in H
           end; simpl in *; eauto with term lang_core.
       - constructor; constructor.
         apply named_list_lookup_err_in; auto.
       - safe_invert HeqH2; subst.
         eapply term_con_congruence; eauto.
         + apply named_list_lookup_err_in; eauto.
         + eapply check_args_proof_sound; eauto.
       - eapply eq_term_subst.
         3: eapply eq_term_by;
         apply named_list_lookup_err_in; eauto.
         + apply named_list_lookup_err_in in HeqH.
           use_rule_in_wf.
           inversion H; subst.
           basic_utils_crush.
         + eapply eq_args_implies_eq_subst.
           eapply check_args_proof_sound; eauto.
       - safe_invert HeqH2; subst.
         eapply sort_con_congruence; eauto.
         + apply named_list_lookup_err_in; eauto.
         + eapply check_args_proof_sound; eauto.
       - eapply eq_sort_subst.
         3: eapply eq_sort_by;
         apply named_list_lookup_err_in; eauto.
         + apply named_list_lookup_err_in in HeqH.
           use_rule_in_wf.
           inversion H; subst.
           basic_utils_crush.
         + eapply eq_args_implies_eq_subst.
           eapply check_args_proof_sound; eauto.
     Qed.
  End Inner.

  (*TODO: use named_list for pf instead of list?*)
  Fixpoint check_proof' (p : pf) : option (tree node_result * positive) :=
    match p with
    | [] => Some (empty _, 1%positive)
    | n::p' =>
        @! let (p_res, next) <- check_proof' p' in
           let n_res <- check_node p_res n in
           ret (set next n_res p_res, next + 1)%positive
    end.

  Definition check_proof (p : pf) : option (term * term * sort) :=
    @! let (m, next) <- check_proof' p in
      let (term_eq_result e1 e2 t) <?- get (next - 1)%positive m in
      ret (e1,e2,t).

      Require Import Lia.
      Open Scope positive.
  
  Lemma check_proof'_fresh' p res next
    : check_proof' p = Some (res, next) ->
      forall n', n' >= next ->
      get n' res = None.
  Proof.
    revert res next; induction p;
      unfold tree_all;
      basic_goal_prep;
      repeat lazymatch goal with
        | [H : default = Some _ |- _ ] => safe_invert H
        | [H : Some _ = Some _ |- _ ] => safe_invert H
        end;
      basic_goal_prep;
      eauto;
      repeat case_match';
      basic_goal_prep;
      try congruence.
    safe_invert H.
    rewrite gso by lia.
    eapply IHp; eauto; lia.
  Qed.
  
  Lemma check_proof'_fresh p res next
    : check_proof' p = Some (res, next) ->
      get next res = None.
  Proof.
    intros; eapply check_proof'_fresh'; eauto; lia.
  Qed.
    
  Lemma check_proof'_sound p res next
    : check_proof' p = Some (res, next) ->
      tree_all node_result_sound res.
  Proof.
    revert res next; induction p;
      unfold tree_all;
      basic_goal_prep;
        repeat lazymatch goal with
        | [H : default = Some _ |- _ ] => safe_invert H
        | [H : Some _ = Some _ |- _ ] => safe_invert H
          end;
      basic_goal_prep;
      eauto using check_node_sound;
    repeat case_match';
      basic_goal_prep;
      try congruence.
    safe_invert H; simpl.
    safe_invert HeqH0.
    destruct (Pos.eq_dec n p0).
    {
      subst.
      rewrite gss in H0.
      safe_invert H0.
      eapply check_node_sound; eauto.      
    }
    rewrite gso in H0; eauto.
    eapply IHp; eauto.
  Qed.

  Theorem check_proof_sound p e1 e2 t
    : check_proof p = Some (e1,e2,t) ->
      eq_term l c t e1 e2.
  Proof.
    unfold check_proof.
    remember (check_proof' p) as check.
    destruct check; simpl; try congruence.
    destruct p0; simpl; try congruence.
    repeat case_match;
      basic_goal_prep;
        repeat lazymatch goal with
        | [H : default = Some _ |- _ ] => safe_invert H
        | [H : Some _ = Some _ |- _ ] => safe_invert H
          end;
      try congruence.
    symmetry in Heqcheck.
    apply check_proof'_sound in Heqcheck.
    simpl in *.
    symmetry in HeqH.
    specialize (Heqcheck _ _ HeqH).
    eauto.
  Qed.

  End WithLang.

End WithVar.
