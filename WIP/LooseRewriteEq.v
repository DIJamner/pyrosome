(*TODO: Move to Proof subdir?*)
Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core CutFreeInd.
Import Core.Notations.




Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
          {V_Eqb_ok : Eqb_ok V_Eqb}
          {V_default : WithDefault V}.

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  Notation term := (@term V).
  Notation var := (@var V).
  Notation con := (@con V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).
  
  Notation wf_subst l :=
    (wf_subst (Model:= core_model l)).
  Notation wf_args l :=
    (wf_args (Model:= core_model l)).
  Notation wf_ctx l :=
    (wf_ctx (Model:= core_model l)).

  
  Notation core_eq_subst l :=
    (eq_subst (Model:= core_model l)).
  Notation core_eq_args l :=
    (eq_args (Model:= core_model l)).

  Notation Model := (@Model V term sort).

  
  Lemma wf_term_inv_up_to_conv l c e t
    : wf_lang l ->
      wf_ctx l c ->
      wf_term l c e t ->
      (exists n s c' args t', e = (Term.con n s)
                            /\ In (n, term_rule c' args t') l
                            /\ Core.eq_sort l c t t' [/with_names_from c' s /]
                            /\ wf_args l c s c')
      \/ (exists x t', e = Term.var x /\ In (x,t') c /\ Core.eq_sort l c t t').
  Proof.
    induction 3.
    {
      left; repeat eexists; eauto.
      eapply eq_sort_refl.
      eapply rule_in_wf in H1; eauto; safe_invert H1.
      (*TODO: rule_in not properly automatic*)
      basic_core_crush.
    }
    {
      
      destruct (IHwf_term ltac:(assumption)); break; subst;
        [left | right];
        repeat eexists; eauto.

      2:{ eauto using eq_sort_trans, eq_sort_sym. }
      eapply eq_sort_trans; eauto using eq_sort_trans, eq_sort_sym.
    }
    {
      right; repeat eexists; eauto.
      basic_core_crush.
    }
  Qed.

  Section SortOf.
  (*TODO: find defn.,proofs about this*)
  Require Import Utils.Monad.
  Definition sort_of l c e : option sort :=
    match e with
    | Term.var x => named_list_lookup_err c x
    | Term.con n s =>
        @! let (term_rule c' _ t) <?- named_list_lookup_err l n in
          ret t[/with_names_from c' s/]
    end.
  End SortOf.

Section TermsAndRules.
  Context (l : lang)
    (c : ctx).

  (*right-biased; assumes RHS is wf*)
  Inductive eq_term : term -> term -> Prop :=
  | eq_term_by : forall c' name t e1 e2 s1 s2,
      In (name,term_eq_rule c' e1 e2 t) l ->
      (*TODO: make a version that computes to a conjunction of non-fv clauses *)
      Forall2 (fun '(x,e) '(x2,t) => (x = x2) /\ (In x (fv e2) \/ wf_term l c e t[/s2/])) s2 c' ->
      eq_subst s1 s2 ->
      eq_term e1[/s1/] e2[/s2/]
  | eq_term_by_sym : forall c' name t e1 e2 s1 s2,
      In (name,term_eq_rule c' e2 e1 t) l ->
      (*TODO: sim. to above *)
      Forall2 (fun '(x,e) '(x2,t) => (x = x2) /\ (In x (fv e2) \/ wf_term l c e t[/s2/])) s2 c' ->
      eq_subst s1 s2 ->
      eq_term e1[/s1/] e2[/s2/]
  | eq_term_cong : forall n s1 s2,
      eq_args s1 s2 ->
      eq_term (con n s1) (con n s2)
  | eq_term_var : forall x, eq_term (var x) (var x)
  with eq_subst : subst -> subst -> Prop :=
  | eq_subst_nil : eq_subst [] []
  | eq_subst_cons : forall s1 s2,
      eq_subst s1 s2 ->
      forall name e1 e2,
        (* assumed because the output ctx is wf: fresh name c' ->*)
        eq_term e1 e2 ->
        eq_subst ((name,e1)::s1) ((name,e2)::s2)
  (* equiv to Forall2 eq_term *)
  with eq_args : list _ -> list _ -> Prop :=
  | eq_args_nil : eq_args [] []
  | eq_args_cons : forall s1 s2,
      eq_args s1 s2 ->
      forall e1 e2,
        eq_term e1 e2 ->
        eq_args (e1::s1) (e2::s2).

  Inductive eq_sort : sort -> sort -> Prop :=
  | eq_sort_by : forall c' name t1 t2 s1 s2,
      In (name, sort_eq_rule c' t1 t2) l ->
      (*TODO: does the var have to be on both sides?
        In theory just has to be on the typechecked side
        need to have 2 mutual judgments, right and left?
       *)
    (*  all (fun '(n,t) => (var_in n t1 /\ var_in n t1)
      (*TODO:include other disjunct*)
                         \/ exists e, In (n,e) s1 /\ wf_term l c e t[/s1/]) c' ->*)
      eq_subst s1 s2 ->
      eq_sort t1[/s1/] t2[/s2/]
  | eq_sort_by_sym : forall c' name t1 t2 s1 s2,
      In (name, sort_eq_rule c' t1 t2) l ->
      (*TODO: does the var have to be on both sides?
        In theory just has to be on the typechecked side
        need to have 2 mutual judgments, right and left?
       *)
    (*  all (fun '(n,t) => (var_in n t1 /\ var_in n t1)
      (*TODO:include other disjunct*)
                         \/ exists e, In (n,e) s1 /\ wf_term l c e t[/s1/]) c' ->*)
      eq_subst s1 s2 ->
      eq_sort t2[/s1/] t1[/s2/]
  | eq_sort_cong : forall n s1 s2,
       eq_args s1 s2 ->
       eq_sort (scon n s1) (scon n s2).

  Scheme eq_term_ind' := Minimality for eq_term Sort Prop
  with eq_subst_ind' := Minimality for eq_subst Sort Prop
  with eq_args_ind' := Minimality for eq_args Sort Prop.

  Combined Scheme judge_ind
    from eq_term_ind', eq_subst_ind', eq_args_ind'.

  Hint Constructors eq_term eq_sort eq_subst eq_args : lang_core.


  
  Context (wfl : wf_lang l)
    (wfc : wf_ctx l c).


  (*
  Lemma wf_term_fv_ind
    : forall (P : Term.ctx V -> Term.term V -> Term.sort V -> Prop)
             (Pin := fun c e t => forall n, In n (fv e) -> P c e t),
             (Pin_args := fun c e t => forall n, In n (fv e) -> P c e t),
       (forall (c : Model.ctx) (n : V) (s : list (Term.term V)) (args : list V) (c' : Term.ctx V)
          (t : Term.sort V),
           In (n, term_rule c' args t) l ->
           wf_args l c s c' ->
           Pin c (Term.con n s) t [/with_names_from c' s /]) ->
       (forall (c : Term.ctx V) (e : Term.term V) (t t' : Term.sort V),
        wf_term l c e t -> Pin c e t -> Core.eq_sort l c t t' -> Pin c e t') ->
       (forall (c : list (V * Term.sort V)) (n : V) (t : Term.sort V), In (n, t) c -> Pin c {{e n}} t) ->
       forall (c : Term.ctx V) (t : Term.term V) (s : Term.sort V), wf_term l c t s -> Pin c t s.*)


  Lemma In_flat_map {A B} x (f : A -> _ B) lst
    : In x (flat_map f lst) <-> exists a, In a lst /\ In x (f a).
  Proof.
    induction lst;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
 (* (*TODO: make global in Utils.v?*)
  #[local] Hint Rewrite @In_flat_map : utils.*)

  (*TODO: Move to Utils.v*)
  Hint Constructors Exists : utils.

  Definition wf_args_forall s c' :=
    Forall2 (fun e '(x,t) => wf_term l c e t[/with_names_from c' s/]) s c'.

  (*TODO: Move to Utils.v*)
  Lemma Forall2_ext {A B} (R1 : _ -> _ -> Prop) (R2 : _ -> _ -> Prop) l1 l2
    : (forall (x : A) (y : B), In x l1 -> In y l2 -> R1 x y -> R2 x y) -> Forall2 R1 l1 l2 -> Forall2 R2 l1 l2.
  Proof.
    induction 2; basic_goal_prep; basic_utils_crush.
    constructor; eauto.
  Qed.

                           
  (*TODO: Move to Utils.v*)
  Lemma fresh_with_names_from {A B} (c' : named_list A) (s : list B) name
    : length c' = length s -> fresh name (with_names_from c' s) <-> fresh name c'.
  Proof.
    revert s; induction c'; destruct s;
      basic_goal_prep; try reflexivity; safe_invert H.
    basic_utils_crush.
  Qed.

                           
  (*TODO: move to the right place*)
  Lemma wkn_well_scoped x args (e : term)
    : well_scoped args e -> well_scoped (x :: args) e.
  Proof.
    induction e; basic_goal_prep; basic_term_crush.
    revert dependent l0; induction l0;
      basic_goal_prep; basic_term_crush.
  Qed.
  #[local] Hint Resolve wkn_well_scoped : term.
  
  Lemma wkn_well_scoped_sort x args (e : sort)
    : well_scoped args e -> well_scoped (x :: args) e.
  Proof.
    induction e; basic_goal_prep; basic_term_crush.
    revert dependent l0; induction l0;
      basic_goal_prep; basic_term_crush.
    apply wkn_well_scoped; eauto.
  Qed.
  #[local] Hint Resolve wkn_well_scoped_sort : term.
  
  Lemma wf_args_as_forall s c'
    :  wf_ctx l c' ->
       wf_args l c s c' -> wf_args_forall s c'.
  Proof.
    unfold wf_args_forall.
    induction 2;
      basic_goal_prep;
      constructor; eauto;
      autorewrite with lang_core model in *;
      break.                     
    {
      erewrite strengthen_subst; eauto; basic_core_crush.
      (*TODO: why is this necessary?*)                       
      typeclasses eauto.
    }
    {
      eapply Forall2_ext; eauto.
      intros;
        break.
      clear IHwf_args H0.
      erewrite strengthen_subst; eauto.
      { basic_core_crush. 
        (*TODO: why is this necessary?*)                       
        typeclasses eauto.
      }
      2:{
        rewrite fresh_with_names_from; auto.
        basic_core_crush.
      }      
      rewrite map_fst_with_names_from.
      2:basic_core_crush.
      apply Core.wf_implies_ws in H2;[ | typeclasses eauto | basic_core_crush].
      revert H2 H5; clear.
      induction c';
        basic_goal_prep;
        basic_utils_crush.
      {
        basic_term_crush.
      }
      {
        basic_term_crush.
      }
    }
  Qed.

  
  Definition wf_subst_forall (s : subst) (c' : ctx) :=
    Forall2 (fun pe pt => (fst pe) = (fst pt) /\ wf_term l c (snd pe) (snd pt)[/s/]) s c'.

  Lemma Forall2_and_inv A B (R Q : A -> B -> Prop) l1 l2
    : Forall2 (fun a b => R a b /\ Q a b) l1 l2 <-> Forall2 R l1 l2 /\ Forall2 Q l1 l2.
  Proof.
    split.
    {
      induction 1; basic_goal_prep; basic_utils_crush.
    }
    {
      intros [H1 H2]; revert H2;
        induction H1;
        intro H2; safe_invert H2;
        basic_utils_crush.
    }
  Qed.
  
  Lemma wf_subst_as_forall s c'
    :  wf_ctx l c' ->
       wf_subst l c s c' -> wf_subst_forall s c'.
  Proof.
    (*TODO: copied*)
    
    unfold wf_args_forall.
    induction 2;
      basic_goal_prep;
      constructor; eauto;
      autorewrite with lang_core model in *;
      break.                     
    {
      erewrite strengthen_subst; eauto; basic_core_crush.
      (*TODO: why is this necessary?*)                       
      typeclasses eauto.
    }
    {
      eapply Forall2_ext; eauto.
      2:{  apply IHwf_subst; auto. }
      
      intros;
        break.
      clear IHwf_subst.
      erewrite strengthen_subst; eauto.
      { basic_core_crush. 
        (*TODO: why is this necessary?*)                       
        typeclasses eauto.
      }
      2:{
        eapply subst_name_fresh_from_ctx; eauto.
      }
      {
        simpl in *; subst.
        erewrite wf_subst_dom_eq; eauto.
        revert H5.
        induction H2; basic_goal_prep; basic_core_crush.
      }
    }
  Qed.
  
  (*TODO: Move to a better place?*)
  (*TODO: move to a more suitable location (Core.v?)*)
  Lemma term_sort_canonical e t1
    : wf_lang l -> (*TODO: can I weaken this?*)
      wf_ctx l c ->
      wf_term l c e t1 ->
      forall t2, sort_of l c e = Some t2 ->
                 wf_term l c e t2.
  Proof.
    induction 3; basic_goal_prep.
    {
      revert H3; case_match; [| congruence].
      case_match; basic_utils_crush.
      apply named_list_lookup_err_in in HeqH3.
      pose proof (in_all_fresh_same _ _ _ _ ltac:(eauto using wf_lang_ext_all_fresh) H1 HeqH3).
      safe_invert H3.
      eauto with lang_core. (*TODO: why is crush slow?*)
    }
    1:eauto.
    {
      eapply wf_term_var; basic_utils_crush.
    }
  Qed.

  (*use with term_sorts_eq *)
  Lemma term_sort_canonical_equiv e t1
    : wf_lang l -> (*TODO: can I weaken this?*)
      wf_ctx l c ->
      wf_term l c e t1 ->
      forall t2, sort_of l c e = Some t2 ->
                 Core.eq_sort l c t1 t2.
  Proof.
    intros; eapply term_sorts_eq; eauto using term_sort_canonical.
  Qed.

  (*TODO: move to Term.v*)
  (*
  Lemma subst_lookup_incl s s' n
    : incl s s' -> all_fresh s' -> In n (map fst s) -> subst_lookup s' n = subst_lookup s n.
  Proof.
    unfold  subst_lookup.
   *)

  Lemma wkn_well_scoped_incl
    : forall (x : V) (args args' : list V) (e : term),
      incl args args' -> well_scoped args e -> well_scoped args' e.
  Proof.
    (* Note: a different proof should work for the generic version *)
    induction e;
      basic_goal_prep;
      basic_term_crush.
    revert dependent l0.
    induction l0;
      basic_goal_prep;
      basic_term_crush.
  Qed.

  
  Lemma wkn_well_scoped_incl_sort
    : forall (x : V) (args args' : list V) (e : sort),
      incl args args' -> well_scoped args e -> well_scoped args' e.
  Proof.
    (* Note: a different proof should work for the generic version *)
    induction e;
      basic_goal_prep;
      basic_term_crush.
    revert dependent l0.
    induction l0;
      basic_goal_prep;
      basic_term_crush.
    eapply wkn_well_scoped_incl; eauto.
  Qed.

  
  (* TODO: move to Utils*)
  Lemma named_list_lookup_None_default A (d:A) lst n
    :  None = named_list_lookup_err lst n ->
       d = named_list_lookup d lst n.
  Proof.
    induction lst;
      basic_goal_prep;
      try case_match;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  (* TODO: move to Utils*)
    Lemma named_list_lookup_as_err A (d : A) lst n
    : In n (map fst lst) ->
      named_list_lookup d lst n = @unwrap_with_default _ d (named_list_lookup_err lst n).
    Proof.
      induction lst;
      basic_goal_prep;
      try case_match;
      basic_goal_prep;
        basic_utils_crush.
    Qed.

  Lemma named_list_lookup_eq A (d d' : A) lst lst' n
    : d = d' ->          
      named_list_lookup_err lst n = named_list_lookup_err lst' n ->
      named_list_lookup d lst n = named_list_lookup d' lst' n.
  Proof.
    intro; subst.
    my_case Hlst (named_list_lookup_err lst n);
      my_case Hlst' (named_list_lookup_err lst' n);
      basic_utils_crush.
    {
      rewrite ?named_list_lookup_as_err by basic_utils_crush.
      congruence.
    }
    {
      rewrite <- !named_list_lookup_None_default by basic_utils_crush.
      reflexivity.
    }
  Qed.      
    
  (*TODO:to prove generically, need to add wkn_well_scoped to typeclass*)
  Lemma strengthen_subst_incl_term
    : forall (s s' : list (V * _)) (a : term),
        well_scoped (map fst s) a -> all_fresh s' -> incl s s' -> a [/s' /] = a [/s /].
  Proof.
    intros until a; revert s s';
      induction a;
      basic_goal_prep;
      basic_term_crush.
    {
      unfold subst_lookup.
      apply named_list_lookup_eq; eauto.
      my_case Hlst (named_list_lookup_err s' n);
        my_case Hlst' (named_list_lookup_err s n);
        symmetry in Hlst;
        symmetry in Hlst';
        basic_utils_crush.
      all: try eapply named_list_lookup_err_in in Hlst (* || eapply named_list_lookup_none in Hlst*).
      all: try eapply named_list_lookup_err_in in Hlst' (*|| eapply named_list_lookup_none in Hlst'*).
      {
        eapply in_all_fresh_same; eauto.
      }
      {
        rewrite named_list_lookup_none_iff in Hlst'.
        basic_utils_crush.
      }
      {
        rewrite named_list_lookup_none_iff in Hlst.
        basic_utils_crush.
      }
    }
    {
      revert dependent l0.
      induction l0;
        basic_goal_prep;
        basic_term_crush.
      apply H3; eauto.
    }
  Qed.

      
  (*TODO:to prove generically, need to add wkn_well_scoped to typeclass*)
  Lemma strengthen_subst_incl_sort
    : forall (s s' : list (V * _)) (a : sort),
        well_scoped (map fst s) a -> all_fresh s' -> incl s s' -> a [/s' /] = a [/s /].
  Proof.
    intros until a; revert s s';
      destruct a;
      basic_goal_prep;
      basic_term_crush.
    {
      revert dependent l0.
      induction l0;
        basic_goal_prep;
        basic_term_crush.
      apply strengthen_subst_incl_term; eauto.
    }
  Qed.
   
  
  Lemma wf_subst_forall_in' n0 t' c' e' s s'
    : all_fresh s' ->
      wf_ctx l c' ->
      incl s s' ->
      wf_subst l c s c' ->
      (*Forall2 (fun pe pt => (fst pe) = (fst pt) /\ wf_term l c (snd pe) (snd pt) [/s' /]) s c' ->*)
      In (n0, t') c' ->
      In (n0, e') s ->
      wf_term l c e' t' [/s' /].
  Proof.
    intros Hfr.    
    revert c';
      induction s;
      basic_goal_prep; try tauto.
    safe_invert H1; basic_goal_prep; subst.
    safe_invert H.
    basic_utils_crush.
    {
      replace t'[/s'/] with t'[/s/]; auto.
      symmetry; apply strengthen_subst_incl_sort; auto.
      basic_core_crush.
    }
    {
      assert (e' = t).
      {
        eapply in_all_fresh_same; eauto.
      }
      subst.
      replace t'[/s'/] with t'[/s/]; auto.
      symmetry; apply strengthen_subst_incl_sort; auto.
      basic_core_crush.
    }
  Qed.

  Lemma map_first_eq_all_fresh A B (l1 : named_list A) (l2 : named_list B)
    : map fst l1 = map fst l2 -> all_fresh l1 -> all_fresh l2.
  Proof.
    revert l2; induction l1;
      destruct l2;
      basic_goal_prep;
      basic_utils_crush.
    unfold fresh in *.
    congruence.
  Qed.
  
  Lemma wf_subst_forall_in n0 t' c' e' s
    : wf_ctx l c' ->
      wf_subst l c s c' ->
      In (n0, t') c' ->
      In (n0, e') s ->
      wf_term l c e' t' [/s/].
  Proof.
    intros; eapply wf_subst_forall_in'; eauto.
    2: basic_utils_crush.
    eapply map_first_eq_all_fresh.
    {
      symmetry;
        eapply wf_subst_dom_eq; eauto.
    }
    basic_core_crush.
  Qed.

  Lemma wf_subst_forall_to_wf_subst' s
    :  forall c' s', Forall2 (fun pe pt => fst pe = fst pt
                                           /\ wf_term l c (snd pe) (snd pt) [/s' /]) s c' ->
                     incl s s' ->
                     all_fresh s' ->
                     wf_ctx l c' ->
                     wf_subst l c s c'.
  Proof.
    induction s;
      intros until s'; intro H;
      safe_invert H;
      basic_goal_prep;
      basic_core_crush.
    erewrite <- strengthen_subst_incl_sort; eauto.
    replace (map fst s) with (map fst l').
    1:basic_core_crush.
    revert H4; clear; intro H4.
    induction H4;
      basic_goal_prep;
      basic_utils_crush.
  Qed.

  
  Lemma wf_subst_forall_map_fst s c'
    : wf_subst_forall s c' -> map fst s = map fst c'.
  Proof.
     induction 1;
      basic_goal_prep;
       basic_utils_crush.
  Qed.
  
  Lemma wf_subst_forall_to_wf_subst s c'
    : wf_subst_forall s c' ->
      wf_ctx l c' ->
      wf_subst l c s c'.
  Proof.
    intros; eapply wf_subst_forall_to_wf_subst'.
    1:apply H.
    all: basic_core_crush.
    eapply map_first_eq_all_fresh.
    1:symmetry;eapply wf_subst_forall_map_fst; eauto.
    basic_core_crush.
  Qed.

  (*TODO: move to core *)
  Lemma wf_ctx_app_tl c1 c2
    : wf_ctx l (c1++c2) ->
      wf_ctx l c2.
  Proof.
    induction c1;
      basic_goal_prep;
      basic_core_crush.
  Qed.


  Notation eq_sortR c t t' := (t = t' \/ Core.eq_sort l c t t').

  
  Lemma invert_wf_term_by_mod_conv n c' args t s t'
    : In (n, term_rule c' args t) l ->
      wf_term l c (Term.con n s) t' ->
      wf_args l c s c'
      /\ eq_sortR c t [/with_names_from c' s /] t'.
  Proof.
    intros Hin H.
    remember (con n s) as e.
    revert Heqe.
    induction H;
      basic_goal_prep;
      basic_core_crush.
    {
      pose proof (in_all_fresh_same _ _ _ _ ltac:(eauto with lang_core) Hin H) as H3.
      safe_invert H3.
      assumption.
    }
    {
      pose proof (in_all_fresh_same _ _ _ _ ltac:(eauto with lang_core) Hin H) as H3.
      safe_invert H3.
      intuition idtac.
    }
    {
      right.
      eapply eq_sort_trans; eassumption.
    }
  Qed.


  Lemma with_names_from_app A B (l1 : named_list A) (l2 : list B) l1' l2'
    : length l1 = length l2 ->
      with_names_from (l1++l1') (l2++l2')
      =with_names_from l1 l2
         ++ with_names_from l1' l2'.
  Proof.
    revert l2;
      induction l1;
      destruct l2;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  
  Lemma ctx_strengthen' c'0 name e0
    : wf_ctx l c'0 ->
      forall c'1 s' s,
        (*all_fresh (c'1++c'0) ->*)
        fresh name (c'1++c'0) ->
        length c'1 = length s' ->
        length c'0 = length s ->
        map (fun t1 : sort => t1 [/(name, e0) :: with_names_from (c'1++c'0) (s'++s) /])
          (map snd c'0)
        = map (fun t1 : sort => t1 [/with_names_from (c'1++c'0) (s'++s) /])
            (map snd c'0).
  Proof.
    induction 1;
      destruct s;
      basic_goal_prep;
      basic_term_crush.
    {
      erewrite strengthen_subst with (a:=v);
        eauto;
        try typeclasses eauto.
      2:{
        rewrite with_names_from_app; eauto.
        basic_goal_prep.
        basic_utils_crush.
        all:rewrite fresh_with_names_from; eauto.
      }
      {
        basic_goal_prep.
        rewrite map_fst_with_names_from; eauto.
        2: {
          rewrite !app_length; simpl; congruence.
        }
        eapply wkn_well_scoped_incl_sort; eauto.
        {
          rewrite map_app.
          eapply incl_appr.
          simpl.
          eapply incl_tl.
          eapply incl_refl.
        }
        basic_core_crush.
      }
    }
    {
      repeat lazymatch goal with
               |- context ctx [?l1 ++ ?e::?l2] =>
                 let x' := context ctx [l1++[e]++l2] in
                 change x'
             end.
      rewrite ! app_assoc.
      rewrite IHwf_ctx; eauto.
      {
        rewrite <- app_assoc; simpl.
        basic_utils_crush.
      }
      {
        rewrite !app_length.
        basic_utils_crush.
      }
    }
  Qed.

   
  Lemma ctx_strengthen c'0 name e0
    : wf_ctx l c'0 ->
      forall s,
        fresh name c'0 ->
        length c'0 = length s ->
        map (fun t1 : sort => t1 [/(name, e0) :: with_names_from c'0 s /])
          (map snd c'0)
        = map (fun t1 : sort => t1 [/with_names_from c'0 s /])
            (map snd c'0).
  Proof.
    intros.
    eapply ctx_strengthen' with (c'1:=[]) (s':=[]); simpl; eauto.
  Qed.

  End TermsAndRules.


Fixpoint concretize (s : list term) (c : ctx) {struct c} :=
  match s, c with
  | [], [] => []
  | _::s', (_,t)::c' =>
      t[/with_names_from c' s'/]::(concretize s' c')
  (* should never happen *)
  | _,_ => []
  end.

Lemma wf_ctx_skipn l c'
  : wf_ctx l c' ->
    forall n,
    wf_ctx l (skipn n c').
Proof.
  induction 1;
    destruct n;
    basic_goal_prep;
    basic_core_crush.
Qed.

(* TODO!!! prune all lemmas above this point. Some are unnecessary. *)
Lemma eq_implies_wf_subst_elts' l c s c'
  : (forall t1 t2,
        Core.eq_sort l c' t1 t2 ->
        forall t2',
          Core.eq_sort l c t1[/s/] t2' ->
          forall x e t', In x (fv t1) ->
                         In (x, e) s ->
                         In (x, t') c' ->
                         (*TODO: be cautious of the /s/*)
                         Core.wf_term l c e t'[/s/])
    /\ (forall t e1 e2,
           Core.eq_term l c' t e1 e2 ->
           forall e2',
             Core.eq_term l c t e1[/s/] e2' ->
             forall x e t', In x (fv e1) ->
                            In (x, e) s ->
                            In (x, t') c' ->
                            Core.wf_term l c e t'[/s/])
    /\ (forall c'' s1 s2,
           Core.eq_arg l c' c'' s1 s2' ->
           forall s2',
             Core.eq_args l c c'' s1[/s/] s2' ->
             forall x e t', In x (fv s1) ->
                            In (x, e) s ->
                            In (x, t') c' ->
                            Core.wf_term l c e t)
.
Proof.
  apply cut_ind


 Lemma subterms_wf_if_in l c e t (s : subst) c' e' t' x c_in
    : wf_lang l ->
      wf_ctx l c ->
      wf_ctx l c' ->
      fresh x c' ->
      wf_sort l c' t' ->
      wf_subst l c s c' ->
      let P c_in e t :=
        c_in = (x,t'):: c' ->
        wf_term l c e[/(x,e')::s/] t[/(x,e')::s/] ->
        In x (fv e) ->
        wf_term l c e' t'[/s/]
      in
      wf_term l c_in e t -> P c_in e t.
  Proof.   
    intros until P.
    eapply wf_judge_ind
      with (P := fun _ _=> True)
           (P0 := P)
           (P1 := fun c s c' => Forall2 (P c) s (concretize s c'));
      subst P;
      repeat basic_goal_prep; auto.
    {
      use_rule_in_wf.
      autorewrite with utils model lang_core term in *.
      break.
      lazymatch goal with
        H : wf_term _ _ (con _ _) ?t [/with_names_from ?c ?s/] [/?s0/] |- _=>
          revert H;
          replace t [/with_names_from c s/] [/s0/]
            with t[/with_names_from c (s[/s0/])/];
          [| erewrite Substable.with_names_from_args_subst, subst_assoc;
             try typeclasses eauto;
             eauto;
             rewrite map_fst_with_names_from;
             basic_core_crush]
      end.
      intro H'.      
      pose proof (invert_wf_term_by_mod_conv H H0 _ _ _ H5 H') as H''.
      destruct H'' as [H'' _].
     (* subst c0.*)
      revert H8 H'' H7 H10 H11.
      clear H' H13 t0 H5 args H12.
      let H := lazymatch goal with H : Model.wf_args _ _ _|- _=> H end in
      induction H;
        basic_goal_prep;
        try tauto.
      subst.
      autorewrite with utils model lang_core term in *.
      safe_invert H7.
      break.
      destruct H10; eauto.
      eapply H13; eauto.
      erewrite subst_assoc; eauto; try typeclasses eauto.
      2:{ rewrite map_fst_with_names_from; basic_core_crush. }
      fold_Substable.
      rewrite <- with_names_from_args_subst.
      exact H12.
    }
    {
      eapply H6; auto.
                        
      (*TDO: how to handle?*)
      replace t0 with t'0 by admit.
      eauto.
    }
    {
      intuition subst.
      basic_goal_prep.
      basic_utils_crush.
      unfold term_subst_lookup in *.
      basic_goal_prep.
      basic_utils_crush.
      erewrite strengthen_subst in H7; eauto;
        try typeclasses eauto.
      all: basic_core_crush.
    }
  Qed.






  Inductive Exists2 (A B : Type) (P : A -> B -> Prop) : list A -> list B -> Prop :=
    Exists2_cons_hd : forall x y l1 l2, P x y -> Exists2 P (x :: l1) (y::l2)
  | Exists2_cons_tl : forall x y l1 l2, Exists2 P l1 l2 -> Exists2 P (x :: l1) (y::l2).

  
  (* TODO: typing info *)
  Inductive subterms_of c : list (term * sort) -> (term * sort) -> Prop :=
  | sub_singleton e t t' : eq_sortR c t t' -> subterms_of c [(e,t)] (e,t')
  | sub_cong s n c' args t' t2 subs
    : In (n, term_rule c' args t') l ->
      eq_sortR c t'[/with_names_from c' s/] t2 ->
      let sorts := (map (fun t => t[/with_names_from c' s/])
                                    (map snd c')) in
      Forall2 (subterms_of c) subs (combine s sorts) ->
      subterms_of c (concat subs) (con n s, t2).
  Hint Constructors subterms_of : lang_core.

  
  Lemma all_app A P (l1 l2 : list A) : all P (l1++l2) <-> all P l1 /\ all P l2.
  Proof.
    induction l1;
      basic_goal_prep;
      basic_utils_crush.
  Qed.
  
  Lemma subterms_wf' e t
    : let P c e t :=
        forall subs,
          subterms_of c subs (e,t) ->
          all (fun p => wf_term l c (fst p) (snd p)) subs
      in
      wf_term l c e t ->
      P c e t.
  Proof.
    intro P.
    eapply wf_judge_ind
      with (P := fun _ _=> True)
           (P0 := P)
           (P1 := fun c s c' => Forall2 (P c) s (map snd c'));
      subst P;
      (* TODO: tactic bug requiring repeat *)
      repeat basic_goal_prep;
      try lazymatch goal with
      | H : subterms_of _ _ _ |- _ => inversion H; subst; clear H
      end;
      repeat basic_goal_prep; intuition subst.
    {
      basic_core_crush.
    }
    {
      eapply wf_term_conv.
      2: eapply eq_sort_sym; eassumption.
      basic_core_crush.
    }
    {
      pose proof (in_all_fresh_same _ _ _ _ ltac:(eauto with lang_core) H H7) as H3.
      inversion H3; subst; clear H3 H H7 H2.
      subst sorts.
      
      revert subs0 H1 H9.
      clear t' args0.
      induction H0;
        basic_goal_prep;
        repeat lazymatch goal with
        | H : Forall2 _ [] _ |- _ => inversion H; subst; clear H
        | H : Forall2 _ _ [] |- _ => inversion H; subst; clear H
        | H : Forall2 _ (_::_) _ |- _ => inversion H; subst; clear H
        | H : Forall2 _ _ (_::_) |- _ => inversion H; subst; clear H
          end;
        basic_goal_prep;
        basic_core_crush.
      rewrite all_app;
        split.
      2:{
        eapply IHwf_args; eauto.
        TODO: want subst in Forall here to be incl?
        eauto.
      apply H1.
      TODO: why is it x::l0?
      revert V_Eqb_ok V_default H0 H8 H1.
      clear.
      induction 3;
        basic_goal_prep.
      {
        inversion H8.
      }
      {
        inversion H1; subst; clear H1.
        lazymatch goal with
        | H : Exists2 _ _ _ |- _ => inversion H; subst; clear H
        | H : Forall2 _ _ _ |- _ => inversion H; subst; clear H
        end;
        basic_core_crush.
      {
        
        eapply IHwf_args; eauto.
    pose proof (eqb_spec e e').
    destruct (eqb e e'); subst; eauto.
  Qed.
 
  Lemma subterm_wf e e' t
    : wf_term l c e t ->
      subterm_of e' e ->
      exists t', wf_term l c e' t'.
  Proof.
    intros.
    pose proof (eqb_spec e e').
    destruct (eqb e e'); subst; eauto.
    eapply (subterm_wf' H); eauto.
  Qed.
  
  Lemma wf_term_fv' e2 t2 t3 x c' s e t c_tmp
    : wf_term l c_tmp e2 t2 ->
      c_tmp = ((x,t)::c') ->
      wf_subst l c s c' ->
      wf_term l c e2[/(x,e)::s/] t3 ->
      In x (fv e2) ->
      fresh x c' ->
      exists t, wf_term l c e t.
  Proof.
    induction 1;
      basic_goal_prep; eauto.
    2:{
      intuition subst; basic_goal_prep.
      basic_utils_crush.
      cbn in H2.
      basic_utils_crush.
    }
    {
      intuition subst; basic_goal_prep.
      (*TODO: need inversion-modulo-sort*)
      inversion H3.
      Proof structure: select e' in s0 where In x (fv e')
      basic_utils_crush.
      assert (Core.eq_sort l c t3 t0
      term_sorts_eq
      apply H1
      unfold (term_subst_lookup
      basic_
      basic_core_crush.


    (forall x e, In (x,e) s -> In x (fv e2) \/ wf_term l c e t[/s'/]) ->
      incl s s' ->
      wf_term l c e2[/s/] t ->
      
      

    Forall (fun '(x,e) => (In x (fv e2) \/ wf_term l c e t[/s'/])) s' ->
      all_fresh s' ->
      wf_term l (c') e2 t ->
      wf_term l c e2[/s'++s/] t ->
      wf_ctx l c' ->
     (* Forall2 (fun (pe : V * term) (pt : V * sort) => fst pe = fst pt /\ wf_term l c (snd pe) (snd pt) [/s'++s /])
        s' c'' ->*)
      Forall2 (fun (pe : V * term) (pt : V * sort) => fst pe = fst pt /\ wf_term l c (snd pe) (snd pt) [/s'++s /])
        s c'.
  Proof.
  Lemma wf_term_fv' e2 t s s' c'
    : Forall2 (fun '(x,e) '(x2,t) => (x = x2) /\ (In x (fv e2) \/ wf_term l c e t[/(s' ++ s)/])) s c' ->
      all_fresh (s'++s) ->
      wf_term l (c') e2 t ->
      wf_term l c e2[/s'++s/] t ->
      wf_ctx l c' ->
     (* Forall2 (fun (pe : V * term) (pt : V * sort) => fst pe = fst pt /\ wf_term l c (snd pe) (snd pt) [/s'++s /])
        s' c'' ->*)
      Forall2 (fun (pe : V * term) (pt : V * sort) => fst pe = fst pt /\ wf_term l c (snd pe) (snd pt) [/s'++s /])
        s c'.
  Proof.
    revert c' s'.
    induction s;
      intros until s'; intro H;
      safe_invert H;
      basic_goal_prep;
      basic_core_crush.
    all:constructor; basic_goal_prep; intuition subst.
    2:{
      replace (s' ++ (v, t0) :: s)
      with ((s' ++ [(v, t0)]) ++ s) in *.
      {
        eapply IHs; eauto.
        (*eapply Forall2_app; eauto.*)
        TODO: needs to be induction on e2 at the end of the day
      }
      all: rewrite <- app_assoc; reflexivity.
    }      
    2:{
      replace (s' ++ (v, t0) :: s)
      with ((s' ++ [(v, t0)]) ++ s) in *.
      1:replace (c'' ++ (v, s0) :: l')
      with ((c'' ++ [(v, s0)]) ++ l') in *.
      {
        eapply IHs; eauto.
        (*eapply Forall2_app; eauto.*)
      }
      all: rewrite <- app_assoc; reflexivity.
    }
    {
      replace s0 [/s' ++ (v, t0) :: s /]
        with s0 [/(v, t0) :: s /].
      {
        eapply wf_subst_forall_in with (c':=  (v, s0) :: l'); eauto.
        all: basic_utils_crush.
        1: eapply wf_ctx_app_tl; eauto.
        constructor; basic_core_crush.
      eapply wf_subst_forall_to_wf_subst; eauto.
      eapply Forall2_app; eauto.
      TODO: need inverse of wf_subst_as_forall
      Lemma wf_term_fv_in e2 t s c'
        : wf_term l c e2[/s/] t ->
          wf_term l c' e2 t ->
          wf_ctx l c' ->
          In v (fv e2) ->
          In (v, t) c' ->
          In (v, e) s ->
          wf_term l c e t[/s/].
  Proof.
    }
      basic_utils_crush.
    ; try
      
      basic_core_crush.
    
    
    
  Lemma wf_term_fv e2 t s2 c'
    : Forall2 (fun '(x,e) '(x2,t) => (x = x2) /\ (In x (fv e2) \/ wf_term l c e t[/s2/])) s2 c' ->
      wf_term l c e2 t ->
      wf_ctx l c' ->     
      wf_subst l c s2 c'.
  Proof.
    intro Hwfe2.
    induction 1;
      basic_goal_prep;
      basic_core_crush.
    {
      eapply wf_subst_forall_in; eauto.
      {
        
      1:basic_core_crush.
      

  Lemma wf_term_fv' e c' s e' t'
    : wf_ctx l c' ->
      wf_subst_forall s c' ->
      forall t, sort_of l c' e = Some t ->
      wf_term l c' e t ->
      wf_term l c e [/s /] t [/s /] ->
      forall n,
        In n (fv e) ->
        In (n, t') c' ->
        In (n, e') s ->
        wf_term l c e' t'[/s/].
  Proof.
    intros wfc' wfs.
    induction e;
      basic_goal_prep.
    {
      intuition subst.
      eapply wf_subst_forall_in; eauto.
      (*TODO: what's the problem w/ eauto & this lemma?*)
      eapply wf_ctx_all_fresh; eauto.
    }
    *)
  
  Lemma wf_term_fv' e c' s n e' t'
    : wf_ctx l c' ->
      wf_subst l c s c' ->
      wf_sort l c' t' ->
      fresh n s ->
      forall t, sort_of l ((n,t')::c') e = Some t ->
      wf_term l ((n,t')::c') e t ->
      wf_term l c e [/(n,e')::s /] t [/(n,e')::s /] ->
      In n (fv e) ->
      wf_term l c e' t'[/s/].
  Proof.
    intros wfc' Hwfs Hfwt' Hfresh.
    induction e;
      basic_goal_prep.
    {
      intuition subst.
      revert H0.
      
      rewrite eqb_refl_true in H,H1 by typeclasses eauto.
      autorewrite with utils term model lang_core in *; subst.
      intro.
      erewrite strengthen_subst in H1; eauto; try typeclasses eauto.
      basic_core_crush.
    }
    {
      revert H0;
        case_match; [|congruence].
      unfold default, option_default.
      case_match; try congruence.
      intro H'; safe_invert H'.

      apply In_flat_map in H3; break.
      pose proof (in_all _ _ H H0).
      eapply wf_term_inv_up_to_conv in H2; auto;
        destruct H2; break; safe_invert H2.

      apply named_list_lookup_err_in in HeqH0.
      
      pose proof (in_all_fresh_same _ _ l _
                    ltac:(eauto with lang_core)
                           H5 HeqH0) as H2.
      safe_invert H2.
      simpl in H4.
      eapply H4; eauto.
      (*TODO: find sort_of lemmas*)      
    }


    
      rewrite 
      eapply wf_term_inv_up_to_conv in H1; auto.
      2: constructor; eauto; admit.
      destruct H; break;
      safe_invert H.
      basic_goal_prep.
      (intuition idtac); [| admit].
      safe_invert H.
      
      idea: |fv t| < |e|
        generalized: use canonical type?
     (* TODO: need e' wf to subst in H1, need subst in H1 to convert H2*)
      eapply eq_sort_subst in H1; cycle 1.
      {
        basic_core_crush.
        admit.
      }
      {
        eapply eq_subst_refl.
        econstructor.
        exact Hwfs.
        instantiate (1:= e').
        unfold Model.wf_term.
      }
      solvable? circularity?
        autorewrite with utils model term lang_core;
        auto.
      3:{
        basic_core_crush.
        safe_invert H.
        erewrite strengthen_subst; eauto; try typeclasses eauto.
        3:{
      TODO: current issue: wsness of t; how to handle?
      t can have n in it, but is eq to something w/out n
      2:replace (map fst s) with (map fst c); [basic_core_crush|].
      TODO: applying s to t/t'; solve w/ wf s
    }
  
  Lemma wf_term_ind_forall
    : forall (P : Term.ctx V -> Term.term V -> Term.sort V -> Prop),
       (forall (c : ctx) (n : V) (s : list (Term.term V)) (args : list V) (c' : Term.ctx V)
               (t : Term.sort V),
           In (n, term_rule c' args t) l ->
           Forall2 (fun e '(x,t) => P c e t[/with_names_from c' s/]) s c' ->
           P c (Term.con n s) t [/with_names_from c' s /]) ->
       (forall (c : Term.ctx V) (e : Term.term V) (t t' : Term.sort V),
        wf_term l c e t -> P c e t -> Core.eq_sort l c t t' -> P c e t') ->
       (forall (c : list (V * Term.sort V)) (n : V) (t : Term.sort V), In (n, t) c -> P c {{e n}} t) ->
       forall (c : Term.ctx V) (t : Term.term V) (s : Term.sort V), wf_term l c t s -> P c t s.
  Admitted.
  
  Lemma wf_term_fv' c' s
    (P := fun c fvs =>
            forall n e' s1 s2 c1 c2 t', In n fvs ->
                             s = s1++ (n,e')::s2 ->
                             c = c1++(n,t')::c2 ->
                             wf_subst l c' s2 c2 ->
                             wf_term l c' e' t'[/s2/])
    : wf_ctx l c' ->
    (forall c s, wf_sort l c s -> True)
    /\ (forall c e t,
           wf_term l c e t ->
           (*forall t',*)
             wf_term l c' e [/s /] t [/s /] -> P c (fv e))
    /\ (forall c s_a c_a,
           wf_args l c s_a c_a ->
           wf_args l c' s_a [/s /] c_a -> P c (flat_map (fv (V:=V)) s_a)).
  Proof.
    intro wfc'.
    apply wf_judge_ind; subst P; basic_goal_prep; intuition try tauto.
  {
    eapply H1; eauto.
    erewrite subst_assoc in H2. 2:basic_core_crush.
    2:{
      subst;
      rewrite map_fst_with_names_from;
      use_rule_in_wf;
      safe_invert H4;
        basic_core_crush.
    }
    revert H2.
    unfold subst_cmp.
    rewrite <- !with_names_from_map_is_named_map.
    intro H2.
    eapply wf_term_inv_up_to_conv in H2;
        destruct H2; break; subst; try congruence.
    safe_invert H2.
      pose proof (in_all_fresh_same _ _ l _
                    ltac:(eauto with lang_core)
                           H7 H) as H2.
      safe_invert H2.
      apply H9.
  }
  {
    eapply H0; eauto.
    subst.
    TODO: to get the proper strengthening, I need to be on a branch where e no longer needs c1
    Will require                                                                         
    replace e [/s1 ++ (n, e') :: s2 /] with e[/s2/] by admit (*TODO: nary strengthening*).
    replace t [/s1 ++ (n, e') :: s2 /] with t[/s2/] by admit (*TODO: nary strengthening*).
    TODO: c0 vs c2
    basic_core_crush.
    TODO: could extend assumptions w/ add'l wfness of, end w/ wfs
    -issue:circularity
           -really want an expanding prefix of s/c'?
                   - induction on s, then on e to find ea. var?
                   
    TODO: use args_forall?
    TODO: needrelationship between s + c; Lemma is false.
    eapply H0; eauto.
    eapply wf_term_conv; eauto.
    admit (*
    TODO: s not wf! need IH output case for eq_sort
           *).
  }
  
  

    
fun (V : Type) (V_Eqb : Eqb V) (l : Rule.lang V) (P : Term.ctx V -> Term.term V -> Term.sort V -> Prop)
  (f : forall (c : Model.ctx) (n : V) (s : list (Term.term V)) (args : list V) (c' : Term.ctx V) (t : Term.sort V),
       In (n, term_rule c' args t) l -> Model.wf_args c s c' -> P c (Term.con n s) t [/with_names_from c' s /])
  (f0 : forall (c : Term.ctx V) (e : Term.term V) (t t' : Term.sort V),
        wf_term l c e t -> P c e t -> Core.eq_sort l c t t' -> P c e t')
  (f1 : forall (c : list (V * Term.sort V)) (n : V) (t : Term.sort V), In (n, t) c -> P c {{e n}} t) =>
fix F (c : Term.ctx V) (t : Term.term V) (s : Term.sort V) (w : wf_term l c t s) {struct w} : P c t s :=
  match w in (wf_term _ c0 t0 s0) return (P c0 t0 s0) with
  | @wf_term_by _ _ _ c0 n s0 args c' t0 i w0 => f c0 n s0 args c' t0 i w0
  | @wf_term_conv _ _ _ c0 e t0 t' w0 e0 => f0 c0 e t0 t' w0 (F c0 e t0 w0) e0
  | wf_term_var _ c0 n t0 i => f1 c0 n t0 i
  end
    


  
  Lemma wf_term_fv c0 e2 t s2
    : wf_term l c0 e2 t ->
      wf_term l c e2 [/s2 /] t [/s2 /] ->
      forall n e t', In n (fv e2) ->
                  In (n,e) s2 ->
                  In (n,t') c0 ->
                  wf_term l c e t'[/s2/].
  Proof.
    induction 1;
      simpl;
      autorewrite with model term.
    {
      erewrite !subst_assoc by admit.
      unfold subst_cmp.
      rewrite <- !with_names_from_map_is_named_map.
      intro wft.
      apply wf_term_inv_up_to_conv in wft;
        destruct wft; break; subst; try congruence.
      safe_invert H1.
      pose proof (in_all_fresh_same _ _ l _ ltac:(eauto with lang_core) H2 H).
      safe_invert H1.
      clear H3.
      intros n e t' Hin; apply In_flat_map in Hin; break.
      intros.
      TODO: missing IH for H4
      TODO: something like in_subst_wf? but not whole subst is wf
      TODO: don't want to do induction here; just want existential
      revert H4; induction H0; inversion 1; subst; auto;
        basic_goal_prep.
      tauto.
      TODO: t too fixed?
      TODO: need to induct over wf_args
      TODO: rule_in_wf_same
      TODO: inversion up to sort_eq
      induction 1; subst.

*)
  
Local Lemma loose_to_strict
  : (forall e1 e2,
           eq_term e1 e2 ->
           forall t,
             wf_term l c e2 t ->
             Core.eq_term l c t e1 e2)
    /\ (forall s1 s2,
           eq_subst s1 s2 ->
           forall c',
             (*concerning case*)
             wf_subst l c s2 c' ->
           core_eq_subst l c c' s1 s2)
    /\ (forall s1 s2,
           eq_args s1 s2 ->
           forall c',
             (*concerning case*)
             wf_args l c s2 c' ->
           core_eq_args l c c' s1 s2).
Proof using.
  apply judge_ind; basic_goal_prep.
  {
    assert (Core.eq_sort l c t[/s2/] t0) by admit.
    eapply eq_term_conv; eauto.
    eapply eq_term_subst; cycle 2.
    {
      eapply Core.eq_term_by; eauto.
    }
    {
      use_rule_in_wf.
      safe_invert H5;
        basic_utils_crush.
    }
    {
      eapply H2.
      use_rule_in_wf.
      autorewrite with utils in *.
      safe_invert H5.
      eapply wf_term_conv in H3.
      2:{ basic_core_crush. }

      rewrite wf_subst_as_forall by auto.
      unfold  wf_subst_forall.
      eapply Forall2_ext; eauto.
      basic_goal_prep; subst; intuition auto.
      TODO: fv lemma
      Fail
    (*TODO: hard case; need add'l invariants*).
    }
  }
  {
    shelve
    (*TODO: hard case; need add'l invariants*).
  }
  {
    apply wf_term_inv_up_to_conv in H1; auto;
    destruct H1; break;
    autorewrite with utils term lang_core in *;
    break;subst; try tauto.
    eapply term_con_congruence; eauto.
  }
  {
    eapply eq_term_refl; eauto.
  }
  { basic_core_crush. }
  {
    safe_invert H3.
    constructor; basic_core_crush.
    eapply H2.
    assumption.
  }
  {
    safe_invert H.
    econstructor.
  }
  {
    safe_invert H3.
    econstructor; eauto.
    eapply H2; eauto.
  }
Qed.
