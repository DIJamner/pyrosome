Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
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

  
    (*TODO: backport these to core.v?*)
    
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
        - admit.
      }
    Admitted.
    
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


  
  (* The type doesn't discriminate between term and sort equalities *)
  Unset Elimination Schemes.
  Inductive pf : Type :=
  (* variable name *)
  | pvar : V -> pf
  (* Rule label, list of subterms*)
  | pcon : V -> list pf -> pf
  | ptrans : pf -> pf -> pf
  | psym : pf -> pf
  | pconv : pf -> pf -> pf.
  Set Elimination Schemes.

  Coercion pvar : V >-> pf.

  (*Stronger induction principle w/ better subterm knowledge
   *)
  Fixpoint pf_ind
           (P : pf -> Prop)
           (IHV : forall n, P(pvar n))
           (IHC : forall n l, all P l ->
                              P (pcon n l))
           (IHT : forall p1, P p1 -> forall p2, P p2 -> P(ptrans p1 p2))
           (IHS : forall p, P p -> P(psym p))
           (IHCV : forall p1, P p1 -> forall p2, P p2 -> P(pconv p1 p2))
           (e : pf) { struct e} : P e :=
    match e with
    | pvar n => IHV n
    | pcon n l =>
        let fix loop l :=
          match l return List.fold_right (fun t => and (P t)) True l with
          | [] => I
          | e' :: l' => conj (pf_ind _ IHV IHC IHT IHS IHCV e') (loop l')
          end in
        IHC n l (loop l)
    | ptrans p0 p1 => IHT p0 (pf_ind _ IHV IHC IHT IHS IHCV p0)
                          p1 (pf_ind _ IHV IHC IHT IHS IHCV p1)
    | psym p0 => IHS p0 (pf_ind _ IHV IHC IHT IHS IHCV p0)
    | pconv p0 p1 => IHCV p0 (pf_ind _ IHV IHC IHT IHS IHCV p0)
                          p1 (pf_ind _ IHV IHC IHT IHS IHCV p1)
    end.

  Fixpoint pf_rect
           (P : pf -> Type)
           (IHV : forall n, P(pvar n))
           (IHC : forall n l,
               List.fold_right (fun t => prod (P t)) unit l ->
               P (pcon n l))
           (IHT : forall p1, P p1 -> forall p2, P p2 -> P(ptrans p1 p2))
           (IHS : forall p, P p -> P(psym p))
           (IHCV : forall p1, P p1 -> forall p2, P p2 -> P(pconv p1 p2))
           (e : pf) { struct e} : P e :=
    match e with
    | pvar n => IHV n
    | pcon n l =>
        let fix loop l :=
          match l return List.fold_right (fun t => prod (P t)) unit l with
          | [] => tt
          | e' :: l' => (pf_rect _ IHV IHC IHT IHS IHCV e', loop l')
          end in
        IHC n l (loop l)
    | ptrans p0 p1 => IHT p0 (pf_rect _ IHV IHC IHT IHS IHCV p0)
                          p1 (pf_rect _ IHV IHC IHT IHS IHCV p1)
    | psym p0 => IHS p0 (pf_rect _ IHV IHC IHT IHS IHCV p0)
    | pconv p0 p1 => IHCV p0 (pf_rect _ IHV IHC IHT IHS IHCV p0)
                          p1 (pf_rect _ IHV IHC IHT IHS IHCV p1)
    end.

  Definition pf_rec := 
    pf_rect
      : forall P : pf -> Set,
        (forall n : V, P n) ->
        (forall (n : V) (l : list pf), fold_right (fun t : pf => prod (P t)) unit l -> P (pcon n l)) ->
        (forall p1 : pf, P p1 -> forall p2 : pf, P p2 -> P (ptrans p1 p2)) ->
        (forall p : pf, P p -> P (psym p)) ->
        (forall p1 : pf, P p1 -> forall p2 : pf, P p2 -> P (pconv p1 p2)) -> forall e : pf, P e.
  

  Section WithLang.

    Context (l : lang).
    (*TODO: change section name?*)
    Context (c : ctx).

    Section Inner.
      Context (check_proof : pf -> option (term * term * sort)).
      Fixpoint check_args_proof (args : list pf) (c' : ctx) :=
        match args, c' with
        | [], [] => Some ([],[])
        | p::args, (_,t)::c'=>
            @! let (lhs, rhs) <- check_args_proof args c' in
               let (e1, e2, t') <- check_proof p in
               (*TODO: use Eqb instance*)
               let ! sort_eq_dec t[/with_names_from c' rhs/] t' in
               ret (e1::lhs, e2::rhs)
        | _,_=> None
        end.
    End Inner.
    
    Fixpoint check_proof (p : pf) : option (term * term * sort) :=
      match p with
      | pvar n =>
          @! let t <- named_list_lookup_err c n in
             ret (var n, var n, t)
      | pcon n s =>
          @! let r <- named_list_lookup_err l n in
             match r with
             | term_rule c' _ t =>
                 @! let (lhs, rhs) <- check_args_proof check_proof s c' in
                    ret (con n lhs, con n rhs, t[/with_names_from c' rhs/])
             | term_eq_rule c' e1 e2 t =>
                 @! let (lhs, rhs) <- check_args_proof check_proof s c' in
                    let lsub := with_names_from c' lhs in
                    let rsub := with_names_from c' rhs in
                    ret (e1[/lsub/],e2[/rsub/],t[/rsub/])
             | _ => None
             end
      | ptrans p0 p1 =>
          @! let (e1, e2, t) <- check_proof p0 in
             let (e1', e2', t') <- check_proof p1 in
             let ! sort_eq_dec t t' in
             let ! term_eq_dec e2 e1' in
             ret (e1, e2', t)
      | psym p =>
          @! let (e1, e2, t) <- check_proof p in
             ret (e2, e1, t)
      | pconv p0 p1 =>
          @! let (t1, t2) <- check_sort_proof p0 in
             let (e1, e2, t) <- check_proof p1 in
             let ! sort_eq_dec t t1 in
             ret (e1, e2, t2)
      end
    
    with check_sort_proof (p : pf) : option (sort * sort) :=
      match p with
      | pvar n => None
      | pcon n s =>
          @! let r <- named_list_lookup_err l n in
             match r with
             | sort_rule c' _ =>
                 @! let (lhs, rhs) <- check_args_proof check_proof s c' in
                    ret (scon n lhs, scon n rhs)
             | sort_eq_rule c' t1 t2 =>
                 @! let (lhs, rhs) <- check_args_proof check_proof s c' in
                    let lsub := with_names_from c' lhs in
                    let rsub := with_names_from c' rhs in
                    ret (t1[/lsub/], t2[/rsub/])
             | _ => None
             end
      | ptrans p0 p1 =>
          @! let (t1, t2) <- check_sort_proof p0 in
             let (t1', t2') <- check_sort_proof p1 in
             let ! sort_eq_dec t2 t1' in
             ret (t1, t2')
      | psym p =>
          @! let (t1,t2) <- check_sort_proof p in
             ret (t2,t1)
      | pconv _ _ => None
      end.

    Context (wfl : wf_lang l)
            (wfc : wf_ctx l c).

    
  (*TOOD: replace case_match with this? Copied once already*)
  Ltac case_match' :=
    try lazymatch goal with
          [ H :  context [ match ?e with
                           | _ => _
                           end] |- _ ] => revert H
        end;
    case_match.


    
    Lemma pf_checker_sound p
      : (forall t1 t2,
        check_sort_proof p = Some (t1, t2) ->
        eq_sort l c t1 t2)
    /\ (forall t e1 e2,
           check_proof p = Some (e1, e2, t) ->
           eq_term l c t e1 e2).
    Proof.
      induction p;
        split;
        basic_goal_prep;
        (*weed out trivial goals for efficiency*)
        try congruence;
        repeat case_match';
        basic_goal_prep;
        try congruence;
        repeat lazymatch goal with
        | [H : Some _ = Some _ |- _ ] => safe_invert H
               end.
      - constructor; constructor.
        + clear HeqH; induction wfc; simpl.
          * apply NoDup_nil.
          * apply NoDup_cons; trivial.
            apply IHw; trivial.
        + eapply named_list_lookup_err_in; eauto.
      - safe_invert HeqH3.
        eapply sort_con_congruence; eauto.
        + eapply named_list_lookup_err_in; eauto.
        + {
            clear HeqH0.
            revert H c0 l4 l5 HeqH2.
            induction l0;
              basic_goal_prep;
              repeat case_match';
              try congruence;
              basic_goal_prep;
              basic_core_crush.
            constructor; eauto.
            eapply H2; auto.
          }
      - safe_invert HeqH3.
        eapply eq_sort_subst; cycle 2.
        + basic_core_crush.
        + with_rule_in_wf_crush.
        + clear HeqH0.
          revert H c0 l3 l4 HeqH2.
          induction l0;
            basic_goal_prep;
            repeat case_match';
            try congruence;
            basic_goal_prep;
            basic_core_crush.
          constructor; eauto.
          eapply H2; auto.
      - safe_invert HeqH3.
        eapply term_con_congruence; eauto.
        + eapply named_list_lookup_err_in; eauto.
        + {
            clear HeqH0.
            revert H c0 l4 l5 HeqH2.
            induction l0;
              basic_goal_prep;
              repeat case_match';
              try congruence;
              basic_goal_prep;
              basic_core_crush.
            constructor; eauto.
            eapply H2; auto.
          }
      - safe_invert HeqH3.
        eapply eq_term_subst; cycle 2.
        + basic_core_crush.
        + with_rule_in_wf_crush.
        + clear HeqH0.
          revert H c0 l3 l4 HeqH2.
          induction l0;
            basic_goal_prep;
            repeat case_match';
            try congruence;
            basic_goal_prep;
            basic_core_crush.
          constructor; eauto.
          eapply H2; auto.
      - safe_invert HeqH2.
        eapply eq_sort_trans; eauto.
      - inversion H.
      - autorewrite with utils in *.
        intuition subst.
        eapply eq_term_trans; eauto.
      - autorewrite with utils in *.
        intuition subst.
      - autorewrite with utils in *.
        intuition subst.
      - autorewrite with utils in *.
        intuition subst.
        eapply eq_sort_sym; eauto.
      - autorewrite with utils in *.
        intuition subst.
        eapply eq_term_sym; eauto.
      - autorewrite with utils in *.
        intuition subst.
        eapply eq_term_conv; eauto.
      - autorewrite with utils in *.
        intuition subst.
    Qed.

    End WithLang.
  
End WithVar.
