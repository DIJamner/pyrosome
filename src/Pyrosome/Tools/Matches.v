(* 
 Gallina functions for matching an expression against a pattern
 *)
Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List Int63.
Require PArray.
Import PArray (array, get, set).
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Monad (*TODO: better dep*) PersistentArrayList.
(*TODO: deprecate computewf at some point (in favor of more general tactic based on reduction proofs) *)
From Pyrosome Require Import Theory.Core Elab.Elab Tools.ComputeWf Tools.Linter Proof.TreeProofs Tools.Int63Renaming.

Import Core.Notations.

Section Int63Matches.
  
Notation named_list := (@named_list int).
Notation named_map := (@named_map int).
Notation term := (@term int).
Notation ctx := (@ctx int).
Notation sort := (@sort int).
Notation subst := (@subst int).
Notation rule := (@rule int).
Notation lang := (@lang int).
Notation pf := (@pf int).

  
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

  
  (*TODO: move to Utils.v, use instead of compute_fresh for performance *)
  Definition inb {A} `{Eqb A} (a : A) (l : list A) : bool := existsb (eqb a) l.
    
Definition freshb {A} x (l : named_list A) : bool := negb (inb x (map fst l)).

(* constructs the union of the two lists viewed as maps,
   choosing the second list when they disagree*)
Fixpoint unordered_merge_unsafe {A} (l1 l2 : named_list A) :=
  match l1 with
  | [] => l2
  | (n,e)::l1' =>
    (if freshb n l2 then [(n,e)] else [])
      ++ (unordered_merge_unsafe l1' l2)
  end.

Section InnerLoop.
  Context (matches_unordered : forall (e pat : term), option subst).
  Fixpoint args_match_unordered (s pat : list term) : option subst :=
       match pat, s with
       | [],[] => @! ret []
       | pe::pat',e::s' =>
         @! let res_e <- matches_unordered e pe in
            let res_s <- args_match_unordered s' pat' in
            ret (unordered_merge_unsafe res_e res_s)                          
       | _,_ => None
       end.
End InnerLoop.

(* Finds the subst s such that s >= acc, e = pat[/s/]
   and (map fst s) = FV(e) U (map fst acc), if such a substitution exists.
   Behavior intentionally unspecified otherwise.
*)
Fixpoint matches_unordered (e pat : term) : option subst :=
  match pat, e with
  | var px, _ => Some ([(px,e)])
  | con pn ps, con n s =>
    if eqb pn n then args_match_unordered matches_unordered s ps else None
  | _,_ => None
end.

(*
Definition matches_unordered e pat :=
  @! s <- matches_unordered_fuel (term_depth pat) e pat;
     ! e == pat[/s/]; (* since we don't check merges, we check post-hoc *)
     ret s.
 *)

Fixpoint order_subst' s args : option subst :=
  match args with
  | [] => @! ret []
  | x::args' =>
    @! let e <- named_list_lookup_err s x in
       let s' <- order_subst' s args' in
       ret ((x,e)::s')
  end.


Definition order_subst s args :=
  (*guarantees that args is a permutation of (map fst s)
    if this function returns a result.
   *)
  if Nat.eqb (length s) (length args) then order_subst' s args else None.


Definition matches_unordered_sort (t pat : sort) :=
  match t, pat with
  | scon n s, scon n_pat s_pat =>
    if eqb n n_pat then
      (* multiply depth by 2 because each level consumes 1 fuel for term
     and 1 for its args
       *)
      args_match_unordered matches_unordered s s_pat
    else None
  end.
          
(* Note that 'args' is critical to getting the order of the output subst correct.
   FV(pat) must be a permutation of args to get a result.
 *)
Definition matches (e pat : term) (args : list int) : option subst :=
  @! let s <- matches_unordered e pat in
     let s' <- order_subst s args in
     (* this condition can fail because merge doesn't check for conflicts *)
     let !Term.eq_term e pat[/s'/] in
     ret s'.

Definition matches_sort t pat (args : list int) : option subst :=
  @! let s <- matches_unordered_sort t pat in
     let s' <- order_subst s args in
     (* this condition can fail because merge doesn't check for conflicts *)
     let !Term.eq_sort t pat[/s'/] in
     ret s'.

(*If the LHS of a term eq rule directly applies to e, 
  return the rule name and s such that LHS[/s/] = e.
  Rules are scanned from the root of the language.
 *)

  Section WithCtx.

    Context (l : array rule).
    Context (c : array sort).

    
    Fixpoint project_term_r p :=
      match p with
      | pcon n s =>
          let s' := map project_term_r s in
          match get l n with
          | (term_rule c' _ _) =>
              con n s'
          | (term_eq_rule c' _ e _) =>
              e[/with_names_from c' s'/]
          | _ => default
          end
      | ptrans p1 p2 => project_term_r p2
      | psym p1 => project_term_l p1
      | pconv p _ => project_term_r p
      | pvar x => var x
      end
    with project_term_l p :=
           match p with
           | pcon n s =>
               let s' := map project_term_l s in
               match get l n with
               | (term_rule c' _ _) =>
                   con n s'
               | (term_eq_rule c' e1 _ _) =>
                   e1[/with_names_from c' s'/]
               | _ => default
               end
           | ptrans p1 p2 => project_term_l p1
           | psym p1 => project_term_r p1
           | pconv p _ => project_term_l p
           | pvar x => var x
           end.
    
    Fixpoint project_sort_r p :=
      match p with
      | pcon n s =>
          let s' := map project_term_r s in
          match get l n with
          | (sort_rule c' _) =>
              scon n s'
          | (sort_eq_rule c' t1 t2) =>
              t2[/with_names_from c' s'/]
          | _ => default
          end
      | ptrans p1 p2 => project_sort_r p2
      | psym p1 => project_sort_l p1
      | pconv p _ => default
      | pvar x => default
      end
        with project_sort_l p :=
      match p with
      | pcon n s =>
          let s' := map project_term_l s in
          match get l n with
          | (sort_rule c' _) =>
              scon n s'
          | (sort_eq_rule c' t1 t2) =>
              t1[/with_names_from c' s'/]
          | _ => default
          end
      | ptrans p1 p2 =>  project_sort_l p1
      | psym p1 => project_sort_r p1
      | pconv p _ => default
      | pvar x => default
      end.
    
      
    
    (*TODO: move to term or treeproofs*)
    (*TODO: requires c, thread through*)
    (* returns the sort of a term, _assuming it is well-formed_ *)
    Fixpoint sort_of p : sort :=
      match p with
      | pvar x => get c x
      | pcon n s =>
          let s' := map project_term_r s in
          match get l n with
          | (term_rule c' _ t) => t[/with_names_from c' s'/]
          | (term_eq_rule c' _ _ t) => t[/with_names_from c' s'/]
          | _ => default
          end
      | ptrans p1 p2 => sort_of p1
      | psym p1 => sort_of p1
      | pconv p _ => project_sort_r p
      end.

  Section Inner.
    Context (step_term : term -> sort -> pf).

    (*TODO: return option?*)
    Fixpoint step_args (s: list term) (c':ctx) : list pf :=
      match s, c' with
      | [], _ => []
      | _,[] => []
      | e::s, (n,t)::c' =>
          (step_term e t[/with_names_from c' s/])::(step_args s c')
      end.

    (* TODO: use sort eqns *)
    (* TODO: make option?*)
    Definition step_sort t : option pf :=
      match t with
      | scon n s =>
          match get l n with
          | sort_rule c' _ => Some (pcon n (step_args s c'))
          | _ => None
          end
      end.

    Definition cast_by_step t2 p : option pf :=
      let t1 := sort_of p in
      (*branch is an optimization, not necessary for correctness*)
      if Term.eq_sort t1 t2 then Some p
      else @! let p1 <- step_sort t1 in
              let p2 <- step_sort t2 in
              ret pconv (ptrans p1 (psym p2)) p.

    
    Fixpoint cast_args_by_step c' s pfs : option (list pf) :=
      match c', s, pfs with
      | [], [], [] => Some []
      | (n,t)::c', e::s, p::pfs =>
          @! let pfs' <- cast_args_by_step c' s pfs in
            let p' <- cast_by_step t[/with_names_from c' s/] p in
            ret p'::pfs'
      | _, _, _ => None
      end.
    
    Fixpoint pf_refl e : option pf :=
      match e with
      | var x => Some (pvar x)
      | con n s =>
          @! let (term_rule c' _ _) <?- Some (get l n) in
            let refls <- list_Mmap pf_refl s in
            let pfs' <- cast_args_by_step c' s refls in
            ret pcon n pfs'
      end.
  
    (* if the top level of the term takes a step, return it *)
    (*
    TODO: parameterize by e's type?
    need to wrap recursively w/ pconvs to reduce types
     *)
    Fixpoint step_redex_term (l' : lang) (e : term)
      : option (pf * term) :=
      match l' with
      | [] => None
      | (n,term_eq_rule c' e1 e2 t')::l' =>
          match step_redex_term l' e with
          | Some e' => Some e'
          | None => @! let s <- matches e e1 (map fst c') in
                      let s' <- list_Mmap (fun '(n,e) =>
                                             @!let ep <- pf_refl e in
                                               (cast_by_step (named_list_lookup default c' n)[/s/] ep))
                                     s in
                       (*
                         for (n,t) & e in c&s:
                         let t := t[/s/]
                         let t' := typeof e
                         cast_by_step l t' t e
                        *)
                       (*todo: pconv for type*)
                       ret (pcon n s', e2[/s/])
          end
      | _::l' => step_redex_term l' e
      end.

      Section StepTermInner.
        Context (step_term_n : term -> option (pf * term)).

        (*invariant: if it returns cong l,
   then l contains a nonempty list *)
        Definition step_subterm e : option (pf * term) :=
          match e with
          | var x => None
          | con name s =>
              let osteps := map step_term_n s in
              if forallb (fun (ma: option _) => if ma then false else true) osteps
              then None
              else
                @! let (term_rule c' _ _) <?- Some (get l name) in
                  let refls <- list_Mmap (fun e => option_map (fun p => (p, e)) (pf_refl e)) s in
                  let steps := map (uncurry unwrap_with_default) (combine refls osteps) in
                  let (arg_steps, args) := split steps in
                  let pfs' <- cast_args_by_step c' s arg_steps in
                  ret (pcon name pfs', con name args)
          end.

        Definition step_term_one_traversal l e
          : option (pf * term) :=
          match step_subterm e with
          | Some p => Some p
          | None => step_redex_term l e
          end.

      End StepTermInner.


      Fixpoint step_term_opt l n e {struct n}
        : option _ :=
        match n with
        | 0 => None
        | S n' =>
            @! let (step,e') <- step_term_one_traversal (step_term_opt l n') l e in
              match step_term_opt l n' e' with
                (*TODO: transitivity casts*)
               | Some (rst_steps, e'') => @! ret (ptrans step rst_steps, e'')
               | None => @! ret (step, e')
               end
        end.

  End Inner.

  (*TODO: what to do with T; currently unused, but probably shouldn't be*)
  Fixpoint step_term' l (n : nat) (e : term) (t : sort) {struct n} : pf :=
    match n with
      (*TODO: do I care if the 0 case is valid?*)
    | 0 => pcon default []
    | S n =>
        match step_term_opt (step_term' l n) l n e with
        | Some (pf,_) => pf
        (*TODO: check that the unwrap always succeeds*)
        | _ => unwrap_with_default (pcon default []) (pf_refl (step_term' l n) e)
        end
    end.
    
  End WithCtx.
  
  (*TODO: find a better location for this?*)
  Definition named_list_to_array {A} `{WithDefault A} (l : named_list A) : array A :=
    let sz := add (fold_left PArrayList.max (map fst l) 0) 1 in
    let acc := PArray.make sz default in
    fold_left (fun acc '(i,a) => set acc i a) l acc.
  
  Definition step_term (l : lang) (c : ctx) (n : nat) e t : pf :=
    let l_arr := named_list_to_array (H:= sort_rule [] []) l in
    let c_arr := named_list_to_array c in
    step_term' l_arr c_arr l n e t. 
  

End Int63Matches.
  

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
Notation pf := (@pf V).

  
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
  
  Import StateMonad.
  Definition step_term_V' (l : lang) (c : ctx) n e t : state (renaming V) _ :=
    @! let l' <- rename_lang l in
      let c' <- rename_ctx c in
      let e' <- rename_term e in
      let t' <- rename_sort t in
      ret step_term l' c' n e' t'.

  Definition step_term_V (l : lang) (c : ctx) n e t : pf :=
    (*TODO: magic number*)
    let ren := empty_rename 500 in
    let (p,ren') := step_term_V' l c n e t ren in
    unrename_pf ren' p.
  
  

Lemma wf_args_cons2
     : forall (l : lang) (c : ctx) (s : list term) (c' : named_list sort) 
         (name name': V) (e e': term) (t t' : sort),
       wf_term l c e t [/with_names_from c' s /] ->
       wf_term l c e' t' [/with_names_from ((name,t)::c') (e::s) /] ->
       wf_args l c s c' -> wf_args l c (e'::e :: s) ((name',t')::(name, t) :: c').
Proof.
  eauto with lang_core.
Qed.

Lemma eq_args_cons2
     : forall (l : lang) (c : ctx) (s1 s2 : list term) (c' : named_list sort) 
         (name name': V) (e1 e2 e1' e2': term) (t t' : sort),
       eq_args l c c' s1 s2 ->
       eq_term l c t [/with_names_from c' s2 /] e1 e2 ->
       eq_term l c t' [/with_names_from ((name,t)::c') (e2::s2) /] e1' e2'->
       eq_args l c ((name',t')::(name, t) :: c') (e1'::e1 :: s1) (e2'::e2 :: s2) .
Proof.
  eauto with lang_core.
Qed.

Lemma eq_term_by_with_subst name l c c' e1 e2 t s 
  : wf_lang l ->
    In (name, term_eq_rule c' e1 e2 t) l ->
    wf_subst l c s c' ->
    eq_term l c t[/s/] e1[/s/] e2[/s/].
Proof.
  intros.
  eapply eq_term_subst; [| eapply eq_subst_refl; eassumption
                         | eapply eq_term_by; eassumption].
  with_rule_in_wf_crush.
Qed.


(*TODO: put in core; really should already exist *)
Lemma lang_ext_monotonicity l1 l2 l
  : wf_lang_ext l1 l -> incl l1 l2 -> all_fresh (l ++ l2) -> wf_lang_ext l2 l.
Proof.
  induction 1; basic_goal_prep; basic_core_crush.
  eapply wf_rule_lang_monotonicity; eauto.
  eauto with utils.
Qed.


(*TODO: for removing redundant goals from term_cong*)
Lemma term_sorts_eq l c e t1
  : wf_lang l -> (*TODO: can I weaken this?*)
    wf_ctx l c ->
    wf_term l c e t1 ->
    forall t2, wf_term l c e t2 ->
               eq_sort l c t1 t2.
Proof.
  induction 3.
  {
    remember (con n s) as e.
    intros t2 wfe; revert t2 wfe Heqe.
    induction 1; basic_goal_prep;
    basic_core_firstorder_crush.
    pose proof (in_all_fresh_same _ _ _ _ (wf_lang_ext_all_fresh H) H3 H1) as H'.
    safe_invert H'.
    basic_core_crush.
  }
  {
    intros; 
    basic_core_crush.
  }
  {
    remember (var n) as e.
    intros t2 wfe; revert t2 wfe Heqe.
    induction 1; basic_goal_prep;
    basic_core_firstorder_crush.
    pose proof (in_all_fresh_same _ _ _ _ (wf_ctx_all_fresh H0) H2 H1) as H'.
    basic_core_crush.
  }
Qed.


Lemma sort_subst_nil (t:sort) : t[/[]/] = t.
Proof using .  
  induction t; basic_goal_prep; basic_utils_crush.
  f_equal.
  induction l; basic_goal_prep; basic_utils_crush.
  apply term_subst_nil.
Qed.
Hint Rewrite sort_subst_nil : term.

(**)

(*TODO: use the version in Core.v or move this one there *)
Local Lemma term_con_congruence' l c t name s1 s2 c' args t'
  : In (name, term_rule c' args t') l ->
    t = t'[/with_names_from c' s2/] ->
    wf_lang l ->
    eq_args l c c' s1 s2 ->
    eq_term l c t (con name s1) (con name s2).
Proof.
  intros.
  assert (wf_ctx l c') by with_rule_in_wf_crush.
  rewrite <- (wf_con_id_args_subst c' s1);[| basic_core_firstorder_crush..].
  rewrite <- (wf_con_id_args_subst c' s2);[|basic_core_firstorder_crush..].
  subst.
  change (con ?n ?args[/?s/]) with (con n args)[/s/].
  eapply eq_term_subst; eauto.
  {
    apply eq_args_implies_eq_subst; eauto.
  }
  constructor.
  replace t' with t'[/id_subst c'/].
  {
    eapply wf_term_by; basic_core_crush.
  }
  basic_core_crush.
Qed.  

Lemma elab_lang_nil_nth_tail l_pre l el
  : l = [] ->
    el = [] ->
    elab_lang_ext l_pre l el.
Proof.
  intros; subst; constructor.
Qed.

End WithVar.


#[export] Hint Rewrite sort_subst_nil : term.


(*TODO: adapt to work w/ possible evars in r?*)
Ltac solve_named_list_in_from_value :=
  match goal with
    [|- In ?p ?l] =>
    let x := eval simpl in (In p l) in
        match x with
        | context [(?n, ?r) = (?n', ?r)] =>
          assert (n = n') by reflexivity
        end;
                           apply named_list_lookup_err_in; compute; reflexivity
  end.

Ltac is_term_rule := eapply eq_term_by; solve_named_list_in_from_value.



Ltac eq_term_by s := 
  eapply (eq_term_by _ _ s); solve_in.



Ltac prove_ident_from_known_elabs :=
  eapply lang_ext_monotonicity;
  [typeclasses eauto with auto_elab elab_pfs
  | auto with utils
  | eapply use_compute_all_fresh; compute; reflexivity].

(*TODO: this is still a tactic performance bottleneck;
  reduce number of calls to it
 *)
Ltac prove_from_known_elabs :=
  (*TODO: is this what I want, or something more general?*)
  rewrite <- ?as_nth_tail;
  repeat
    lazymatch goal with
    | |- wf_lang_ext ?l_pre (?l1 ++ ?l2) => apply wf_lang_concat
    | |- wf_lang_ext _ _ => prove_ident_from_known_elabs
    | |- all_fresh _ => apply use_compute_all_fresh; vm_compute; reflexivity
    | |- incl _ _ => simple eapply use_compute_incl_lang; compute; reflexivity
    end.


(*TODO*)


Ltac term_cong :=
  eapply term_con_congruence;
  [ solve_in
  | solve_len_eq
  | vm_compute; reflexivity
  | solve[prove_from_known_elabs]
  | repeat match goal with [|- eq_args _ _ _ _] =>
                           simple apply eq_args_nil
                           || simple eapply eq_args_cons2
                           || simple eapply eq_args_cons
           end].
Ltac term_refl := 
  apply eq_term_refl; shelve (*TODO: solve[repeat t']*).

Ltac compute_wf_subjects :=
  match goal with
  | [|- wf_term ?l ?c ?e ?t] =>
    let c' := eval vm_compute in c in
        let e' := eval vm_compute in e in
            let t' := eval vm_compute in t in
                change_no_check (wf_term l c' e' t')
  | [|- wf_sort ?l ?c ?t] =>
    let c' := eval vm_compute in c in
        let t' := eval vm_compute in t in
            change_no_check (wf_sort l c' t')
  | [|- wf_ctx ?l ?c] =>
    let c' := eval vm_compute in c in
        change_no_check (wf_ctx l c')
  end.

(*TODO: optimize where this is used so that I don't
  duplicate work?
 *)
 Ltac t' :=
  match goal with
  | [|- fresh _ _ ]=> apply use_compute_fresh; vm_compute; reflexivity
  | [|- sublist _ _ ]=> apply (use_compute_sublist Eqb_dec); vm_compute; reflexivity
  | |- In _ _ => solve [solve_in | simpl; intuition fail]
  | |- Model.wf_term _ _ _ => cbn [Model.wf_term core_model]
  | |- wf_term ?l ?c ?e ?t =>
        let c' := eval vm_compute in c in
        let e' := eval vm_compute in e in
        let t' := eval vm_compute in t in
            change_no_check (wf_term l c' e' t');
    tryif first [has_evar c'| has_evar e' | has_evar t']
    then assumption || eapply wf_term_var || eapply wf_term_by'
    else compute_noconv_term_wf
  | [|-wf_args _ _ _ _] => simple apply wf_args_nil
                           || simple eapply wf_args_cons2
                           || simple eapply wf_args_cons
  | [|-wf_subst _ _ _] => constructor
  | |- wf_ctx (Model:= ?m) ?c =>
    let c' := eval vm_compute in c in
        change_no_check (wf_ctx (Model:= m) c');
    tryif has_evar c'
    then assumption || constructor
    else solve_wf_ctx
  | |- wf_sort ?l ?c ?t =>
        let c' := eval vm_compute in c in
        let t' := eval vm_compute in t in
        change_no_check (wf_sort l c' t'); eapply wf_sort_by
  | [|- wf_lang _] => solve[prove_from_known_elabs]
  (*Don't use vm_compute here*)
  | [|- _ = _] => compute; reflexivity
  end.

Ltac t :=
  match goal with
  | [|- fresh _ _ ]=> apply use_compute_fresh; vm_compute; reflexivity
  | [|- sublist _ _ ]=> apply (use_compute_sublist Eqb_dec); vm_compute; reflexivity
  (*Don't use vm_compute here*)
  | [|- In _ _ ]=> apply named_list_lookup_err_in; compute; reflexivity
  | [|- len_eq _ _] => econstructor
  | [|-elab_sort _ _ _ _] => eapply elab_sort_by
  | [|-elab_ctx _ _ _] => econstructor
  | [|-elab_args _ _ _ _ _ _] => eapply elab_args_cons_ex' || econstructor
  | [|-elab_term _ _ _ _ _] => eapply elab_term_var || eapply elab_term_by'
  | [|-wf_term _ _ _ _] => shelve
  | [|-elab_rule _ _ _] => econstructor
  | |- wf_subst _ _ _ _ => apply wf_subst_cons || apply wf_subst_nil
  (*Don't use vm_compute here*)
  | [|- _ = _] => compute; reflexivity
  end.


(*TODO: only works if all variables appear on the lhs*)
Ltac redex_steps_with lang name :=
  let mr := eval vm_compute in (named_list_lookup_err lang name) in
      lazymatch mr with
      | Some (term_eq_rule ?c ?e1p ?e2p ?tp) =>
        lazymatch goal with
        | [|- eq_term ?l ?c' ?t ?e1 ?e2] =>
          let ms := eval vm_compute in (matches e1 e1p (map fst c)) in
              lazymatch ms with
              | Some ?s =>
                replace (eq_term l c' t e1 e2)
                  with (eq_term l c' tp[/s/] e1p[/s/] e2p[/s/]);
                [| reflexivity];
                eapply eq_term_subst;
                [| | eq_term_by name];
                [solve [repeat t']|apply eq_subst_refl; solve [repeat t']]
              | None => fail "lhs" e1 "does not match rule" e1p
              end
        | _ => fail "Goal not a term equality"
        end
      | _ => fail "Rule not found"
      end.


Ltac compute_eq_compilation :=
  match goal with
  |[|- eq_sort ?l ?ctx ?t1 ?t2] =>
   let ctx' := eval vm_compute in ctx in
       let t1' := eval vm_compute in t1 in
           let t2' := eval vm_compute in t2 in
               change_no_check (eq_sort l ctx' t1' t2')
  |[|- eq_term ?l ?ctx ?e1 ?e2 ?t] =>
   let ctx' := eval vm_compute in ctx in
       let e1' := eval vm_compute in e1 in
           let e2' := eval vm_compute in e2 in
               let t' := eval vm_compute in t in
                   change_no_check (eq_term l ctx' e1' e2' t')
  end.


Ltac cbn_eq_goal :=
  unfold Model.eq_sort, Model.eq_term;
  lazymatch goal with
  |[|- eq_sort ?l ?ctx ?t1 ?t2] =>
     let ctx' := eval cbn in ctx in
       let t1' := eval cbn in t1 in
         let t2' := eval cbn in t2 in
           change_no_check (eq_sort l ctx' t1' t2')
  |[|- eq_term ?l ?ctx ?e1 ?e2 ?t] =>
     let ctx' := eval cbn in ctx in
       let e1' := eval cbn in e1 in
         let e2' := eval cbn in e2 in
           let t' := eval cbn in t in
             change_no_check (eq_term l ctx' e1' e2' t')
  end.

Ltac cbn_elab_goal :=
  lazymatch goal with
  | [|- elab_term ?l ?ctx ?e ?ee ?t] =>
      let ctx' := eval cbn in ctx in
        let e' := eval cbn in e in
          let ee' := eval cbn in ee in
            let t' := eval cbn in t in
              change_no_check (elab_term l ctx' e' ee' t')
  end.

Ltac lhs_concrete :=
  lazymatch goal with
  | [|- eq_term _ _ _ ?lhs _] =>
    tryif has_evar lhs then fail 0 "subject" lhs "contains evars"  else idtac
  end.


Ltac step_if_concrete :=
  tryif lhs_concrete
  then lazymatch goal with
       | [|- eq_term ?l ?c' ?t ?e1 ?e2] =>
           (*TODO: 100 is a magic number; make it an input*)
           let x := eval compute in (step_term_V l c' 100 e1 t) in
             eapply TreeProofs.pf_checker_sound with(p:=x);
             [assumption | compute; reflexivity]
       end
  else term_refl.

Ltac reduce_lhs :=
  compute_eq_compilation;
  eapply eq_term_trans;
  [step_if_concrete|];
  compute_eq_compilation.


Ltac reduce_rhs :=
  compute_eq_compilation;
  eapply eq_term_trans;
  [|eapply eq_term_sym;
    step_if_concrete];
  compute_eq_compilation.

Ltac reduce := reduce_lhs; reduce_rhs.

Ltac by_reduction :=
    compute_eq_compilation;
    lazymatch goal with
    | |- eq_term ?l ?c' ?t ?e1 ?e2 =>
        tryif is_ground e1 then
          tryif is_ground e2 then
                let pf_lhs := eval compute in (step_term_V l c' 100 e1 t) in
                  let pf_rhs := eval compute in (step_term_V l c' 100 e2 t) in
                    let pf_both := constr:(TreeProofs.ptrans pf_lhs
                                             (TreeProofs.psym pf_rhs)) in
                  eapply TreeProofs.pf_checker_sound with (p := pf_both);
                                              [ assumption | vm_compute; reflexivity ]
          else let pf_lhs := eval compute in (step_term_V l c' 100 e1 t) in
                  eapply TreeProofs.pf_checker_sound with (p := pf_lhs);
                                              [ assumption | vm_compute; reflexivity ] 
        else tryif is_ground e2 then
                let pf_rhs := eval compute in (step_term_V l c' 100 e2 t) in
                  eapply TreeProofs.pf_checker_sound with (p := TreeProofs.psym pf_rhs);
                                              [ assumption | vm_compute; reflexivity ] 
          else term_refl
    end.

Ltac process_eq_term :=
  cbn_eq_goal;
  match goal with
  (* in general not valid, but (pretty much) always good*)
  | [|- eq_term _ _ _ (var _) _] => term_refl
  (* might be more problematic w/ my left-to-right discipline*)
  | [|- eq_term _ _ _ _ (var _)] => term_refl
  | [|- eq_term ?l _ _ ?e1 ?e2] =>
    tryif is_evar e1; is_evar e2 then shelve
    else (try solve [compute_everywhere l; by_reduction])
  end.

(* elab_term -> maybe (eq_sort * list elab_term)
           should never fail
           shelves goal if both exp and elaborated exp are evars
           otherwise returns goal connecting derived sort to given sort
           and elab_term goals for alll subterms
 *)
Ltac try_break_elab_term :=
  cbn_elab_goal;
  lazymatch goal with
    [|- elab_term _ _ ?e ?ee ?t] =>
    tryif is_evar e; is_evar ee then shelve else
      eapply elab_term_conv;
    [ (eapply elab_term_var; [solve_in])
      || (eapply elab_term_by;[solve_in | break_down_elab_args])
    | try (sort_cong; repeat process_eq_term)
      (*TODO: try because if we have an evar with a subst applied to it, the tactic fails;
                      should be able to make it succeed
       *)
      (*TODO: assumes lang has no sort equations*)]
  end with
        (*elab_args -> list elab_term; should never fail.
        returns goals for explicit terms,
        shelves goals for implicit terms *)
        break_down_elab_args :=
    (eapply elab_args_cons_ex'; [solve_len_eq |repeat try_break_elab_term | break_down_elab_args])
    || (eapply elab_args_cons_im; [break_down_elab_args | shelve (*TODO: what to run here?*)])
    || eapply elab_args_nil.



Ltac break_elab_sort :=
  eapply elab_sort_by; [solve_in |break_down_elab_args].

(*elab_ctx -> list elab_sort; should never fail*)
Ltac break_down_elab_ctx :=
  (eapply elab_ctx_cons;[solve_fresh| break_down_elab_ctx | break_elab_sort] || eapply elab_ctx_nil).

Ltac break_elab_rule :=
  match goal with
  | [|- elab_rule _ (sort_rule _ _) _] =>
    eapply elab_sort_rule; [break_down_elab_ctx | solve_sublist]
  | [|- elab_rule _ (term_rule _ _ _) _] =>
    eapply elab_term_rule; [break_down_elab_ctx | break_elab_sort | solve_sublist]
  | [|- elab_rule _ (term_eq_rule _ _ _ _) _] =>
    eapply eq_term_rule;[ break_down_elab_ctx | break_elab_sort| try_break_elab_term | try_break_elab_term]    
  end.


Ltac cleanup_auto_elab :=
  solve [ repeat t'].
(*TODO: t' is temporary/not general enough*)


Create HintDb elab_pfs discriminated.
#[export] Hint Resolve elab_lang_nil : elab_pfs.
(*TODO: is this still needed?*)
Create HintDb auto_elab discriminated.
#[export] Hint Resolve elab_lang_nil : auto_elab.
(*TODO: do I need this?*)
(* #[export] Hint Resolve Pre.elab_prefix_monotonicity_lang : auto_elab. *)
#[export] Hint Resolve elab_lang_implies_wf : auto_elab.

#[export] Hint Extern 1 (all_fresh _) => apply use_compute_all_fresh; vm_compute; reflexivity : auto_elab.



Ltac split_rule_elab :=
  eapply elab_lang_cons_nth_tail;
  [ compute; reflexivity
  | compute; reflexivity
  | apply use_compute_fresh; compute; reflexivity |
  (*fail 2 since this will be used in a repeat *)
  | solve [ prove_from_known_elabs ] || fail 2 "Could not prove base language wf" |].

Ltac setup_elab_lang :=
  lazymatch goal with
  | |- elab_lang_ext ?pre ?l ?el =>
      lint_lang_ext pre l;
      rewrite (as_nth_tail l); rewrite (as_nth_tail el)
  | _ => fail "Not a language extension wfness goal"
  end; repeat split_rule_elab;
  [apply elab_lang_nil_nth_tail; compute; reflexivity | intro.. ].


Ltac auto_elab :=
  setup_elab_lang;
  first [ unshelve(solve [ break_elab_rule;
                           apply eq_term_refl;
                           cleanup_auto_elab ]);
          try apply eq_term_refl;
          cleanup_auto_elab].

(*TODO: duplicated; find & remove duplicates*)
Ltac unify_evar_fst_eq V :=
  lazymatch goal with
  | [|- (let (x,_) := ?p in x) = ?y] =>
    let p':= open_constr:((y,_:term V)) in
    unify p p';
    compute;
    reflexivity
  end.

Ltac unify_var_names V s c :=
  let H' := fresh in
  assert (len_eq s c) as H';
  [ solve[repeat constructor]| clear H'];
  assert (map fst s = map fst c) as H';
  [ compute; repeat f_equal; unify_evar_fst_eq V | clear H'].

Ltac eredex_steps_with lang name :=
  let mr := eval vm_compute in (named_list_lookup_err lang name) in
      lazymatch mr with
      | Some (term_eq_rule ?c ?e1p ?e2p ?tp) =>
        lazymatch goal with
        | [|- @eq_term ?V _ ?l ?c' ?t ?e1 ?e2] =>
          let s := open_constr:(_:subst V) in
          first [unify_var_names V s c | fail 2 "could not unify var names"];
          first [ replace (eq_term l c' t e1 e2)
                    with (@eq_term V _ l c' tp[/s/] e1p[/s/] e2p[/s/]);
                  [| f_equal; vm_compute; reflexivity (*TODO: is this general?*)]
                | fail 2 "could not replace with subst"];
          eapply (@eq_term_subst V _ l c' s s c);
          [ try solve [cleanup_auto_elab]
          | eapply eq_subst_refl; try solve [cleanup_auto_elab]
          |eapply (@eq_term_by V _ l c name tp e1p e2p); try solve [cleanup_auto_elab]]
        end
      | None =>
        fail 100 "rule not found in lang"
      end.

Ltac estep_under lang rule :=
  eredex_steps_with lang rule
  || (compute_eq_compilation; term_cong; (estep_under lang rule|| term_refl)).


Ltac rewrite_leftwards lang name :=
  first [ eapply eq_term_trans; [estep_under lang name |]
        | eapply eq_term_trans; [|estep_under lang name ]];
  compute_eq_compilation.
