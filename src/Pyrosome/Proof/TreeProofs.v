Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Monad.
From Pyrosome.Theory Require Import Core.
Import Core.Notations.

Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
          {V_Eqb_ok : Eqb_ok V_Eqb}
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

  
  (*TODO: backport these to core.v?
    Variation: t = t'
   *)
    
  Local Lemma term_con_congruence (l : lang) (c c' : ctx)
    t name s1 s2 args t'
      : In (name, term_rule c' args t') l ->
        t = t'[/with_names_from c' s2/] ->
        wf_lang l ->
        eq_args l c c' s1 s2 ->
        eq_term l c t (con name s1) (con name s2).
    Proof.
      intros.
      rewrite <- (wf_con_id_args_subst c' s1); [|basic_core_crush..].
      rewrite <- (wf_con_id_args_subst c' s2); [| basic_core_crush..].
      subst.
      change (con ?n ?args[/?s/]) with (con n args)[/s/].
      eapply eq_term_subst; eauto.
      2:
      {
        apply eq_args_implies_eq_subst; eauto.
      }
      {
        replace t' with t'[/id_subst c'/] by basic_core_crush.
        (* can't use basic_core_crush because it rewrites id subst *)
        eauto with utils model term lang_core.
      }
      basic_core_crush.
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
               let ! eqb t[/with_names_from c' rhs/] t' in
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
             let ! eqb t t' in
             let ! eqb e2 e1' in
             ret (e1, e2', t)
      | psym p =>
          @! let (e1, e2, t) <- check_proof p in
             ret (e2, e1, t)
      | pconv p0 p1 =>
          @! let (t1, t2) <- check_sort_proof p0 in
             let (e1, e2, t) <- check_proof p1 in
             let ! eqb t t1 in
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
             let ! eqb t2 t1' in
             ret (t1, t2')
      | psym p =>
          @! let (t1,t2) <- check_sort_proof p in
             ret (t2,t1)
      | pconv _ _ => None
      end.

    (*TODO: move to Monad.v*)
    Instance sum_monad {Err} : Monad (sum Err) :=
      {
        Mret _ := inr;
        Mbind _ _ f ma :=
          match ma with
          | inr a => f a
          | inl p => inl p
          end
      }.

    (*TODO: use of default will make error reporting worse*)
    Instance sum_default Err `{WithDefault Err} {A} : WithDefault (Err + A) :=
      inl default.

    Instance pf_default : WithDefault pf := pcon default [].

    Definition lift_err {Err} (e:Err) {A} (o : option A) :=
      match o with
      | Some x => inr x
      | None => inl e
      end.

    (*TODO: generalize to MonadErr M E*)
    Notation "'let' ! e |-> err 'in' b" :=
      (if e then b else inl err)
        (in custom monadic_do at level 200, left associativity,
            e constr, b custom monadic_do, err constr at level 100).

    Inductive tp_err :=
    | lang_lookup_err (n : V)
    | ctx_lookup_err (c' : ctx) (x : V)
    | sort_eq_err (t1 t2 : sort)
    | arg_length_err (p : pf)
    (*extra info*)
    | addl_err (e : tp_err) {A} (s : A)
    (* catchall*)
    | pf_invalid_err (p : pf).
    (*TODO: use of default will make error reporting worse*)
    Instance tp_err_default : WithDefault tp_err :=
      pf_invalid_err default.
    
    Section Inner.
      Context (check_proof_err : pf -> tp_err + (term * term * sort)).
      Context (err : pf).
      Fixpoint check_args_proof_err (args : list pf) (c' : ctx) : tp_err + _ :=
        match args, c' with
        | [], [] => inr ([],[])
        | p::args, (_,t)::c'=>
            @! let {(sum _)} (lhs, rhs) <- check_args_proof_err args c' in
               let {(sum _)} (e1, e2, t') <- (check_proof_err p) in
               (*TODO: use Eqb instance*)
               (*TODO: sorts don't line up here*)
               let ! eqb t[/with_names_from c' rhs/] t' |->
                     addl_err (addl_err (sort_eq_err t[/with_names_from c' rhs/] t') "in args checking for: ")
                     err in
               ret {(sum _)} (e1::lhs, e2::rhs)
        | _,_=> inl (arg_length_err err)
        end.
    End Inner.
    
    Fixpoint check_proof_err (p : pf) : tp_err+ (term * term * sort) :=
      match p with
      | pvar n =>
          @! let t <- lift_err (ctx_lookup_err c n) (named_list_lookup_err c n) in
             ret (var n, var n, t)
      | pcon n s =>
          @! let r <- lift_err (lang_lookup_err n) (named_list_lookup_err l n) in
             match r with
             | term_rule c' _ t =>
                 @! let (lhs, rhs) <- check_args_proof_err check_proof_err p s c' in
                    ret (con n lhs, con n rhs, t[/with_names_from c' rhs/])
             | term_eq_rule c' e1 e2 t =>
                 @! let (lhs, rhs) <- check_args_proof_err check_proof_err p s c' in
                    let lsub := with_names_from c' lhs in
                    let rsub := with_names_from c' rhs in
                    ret (e1[/lsub/],e2[/rsub/],t[/rsub/])
             | _ => inl (addl_err (lang_lookup_err n) "expected term rule")
             end
      | ptrans p0 p1 =>
          @! let (e1, e2, t) <- check_proof_err p0 in
             let (e1', e2', t') <- check_proof_err p1 in
             let ! eqb t t' |->
                   addl_err (sort_eq_err t t') "sorts of term transitivity don't match" in
             let ! eqb e2 e1' in
             ret (e1, e2', t)
      | psym p =>
          @! let (e1, e2, t) <- check_proof_err p in
             ret (e2, e1, t)
      | pconv p0 p1 =>
          @! let (t1, t2) <- check_sort_proof_err p0 in
             let (e1, e2, t) <- check_proof_err p1 in
             let ! eqb t t1 |->
                   addl_err (sort_eq_err t t1) "LHS of conv does not match term" in
             ret (e1, e2, t2)
      end
    
    with check_sort_proof_err (p : pf) : tp_err + (sort * sort) :=
      match p return sum _ _ with
      | pvar n => inl (addl_err (pf_invalid_err p) "vars are not sorts")
      | pcon n s =>
          @! let r <- lift_err (ctx_lookup_err c n) (named_list_lookup_err l n) in
             match r with
             | sort_rule c' _ =>
                 @! let (lhs, rhs) <- check_args_proof_err check_proof_err p s c' in
                    ret (scon n lhs, scon n rhs)
             | sort_eq_rule c' t1 t2 =>
                 @! let (lhs, rhs) <- check_args_proof_err check_proof_err p s c' in
                    let lsub := with_names_from c' lhs in
                    let rsub := with_names_from c' rhs in
                    ret (t1[/lsub/], t2[/rsub/])
             | _ => inl (addl_err (lang_lookup_err n) "expected sort rule")
             end
      | ptrans p0 p1 =>
          @! let (t1, t2) <- check_sort_proof_err p0 in
             let (t1', t2') <- check_sort_proof_err p1 in
             let ! eqb t2 t1' |->
                   addl_err (sort_eq_err t2 t1') "sort transitivity failed" in
             ret (t1, t2')
      | psym p =>
          @! let (t1,t2) <- check_sort_proof_err p in
             ret (t2,t1)
      | pconv _ _ => inl (addl_err (pf_invalid_err p) "cannot conv a sort")
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
      - basic_core_crush.
      - safe_invert HeqH3.
        eapply sort_con_congruence; eauto.
        + basic_core_crush.
        + {
            clear HeqH0.
            revert H n0 l4 l5 HeqH2.
            induction l0;
              basic_goal_prep;
              repeat case_match';
              try congruence;
              basic_goal_prep;
              basic_core_crush.
            eapply H2; auto.
          }
      - safe_invert HeqH3.
        eapply eq_sort_subst.
        + basic_core_crush.
        + clear HeqH0.
          revert H n0 l3 l4 HeqH2.
          induction l0;
            basic_goal_prep;
            repeat case_match';
            try congruence;
            basic_goal_prep;
            basic_core_crush.
          eapply H2; auto.
        + basic_core_crush.
      - safe_invert HeqH3.
        eapply term_con_congruence; eauto.
        + basic_core_crush.
        + {
            clear HeqH0.
            revert H n0 l4 l5 HeqH2.
            induction l0;
              basic_goal_prep;
              repeat case_match';
              try congruence;
              basic_goal_prep;
              basic_core_crush.
            eapply H2; auto.
          }
      - safe_invert HeqH3.
        eapply eq_term_subst.
        + basic_core_crush.
        + clear HeqH0.
          revert H n0 l3 l4 HeqH2.
          induction l0;
            basic_goal_prep;
            repeat case_match';
            try congruence;
            basic_goal_prep;
            basic_core_crush.
          eapply H2; auto.
        + basic_core_crush.
      - eapply eq_sort_trans; basic_utils_crush.
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
