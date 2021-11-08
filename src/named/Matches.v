(* 
 Gallina functions for matching an expression against a pattern
 *)
Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Elab ComputeWf.

Import Core.Notations.
Import OptionMonad.


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


(*
Set Default Proof Mode "Ltac2".
*)


(* constructs the union of the two lists viewed as maps,
   choosing the second list when they disagree*)
Fixpoint unordered_merge_unsafe {A} (l1 l2 : named_list A) :=
  match l1 with
  | [] => l2
  | (n,e)::l1' =>
    (if compute_fresh n l2 then [(n,e)] else [])
      ++ (unordered_merge_unsafe l1' l2)
  end.

Section InnerLoop.
  Context (matches_unordered : forall (e pat : term), option subst).
  Fixpoint args_match_unordered (s pat : list term) : option subst :=
       match pat, s with
       | [],[] => do ret []
       | pe::pat',e::s' =>
         do res_e <- matches_unordered e pe;
            res_s <- args_match_unordered s' pat';
            ret (unordered_merge_unsafe res_e res_s)                          
       | _,_ => None
       end.
End InnerLoop.

(* TODO: move to term*)
Fixpoint term_dec (x y : term) {struct x} : {x = y} + {~ x = y}.
  refine (match x,y with
          | var n, var m => if Eqb_dec n m then left _ else right _
          | con n s, con n' s' =>
            if Eqb_dec n n'
            then if list_eq_dec term_dec s s' then left _ else right _
            else right _
          | _, _ => right _
          end).
  all: try let H := fresh in intro H; inversion H; clear H; subst.
  all: basic_term_crush.
Defined.

(* Finds the subst s such that s >= acc, e = pat[/s/]
   and (map fst s) = FV(e) U (map fst acc), if such a substitution exists.
   Behavior intentionally unspecified otherwise.
*)
Fixpoint matches_unordered (e pat : term) : option subst :=
  match pat, e with
  | var px, _ => Some ([(px,e)])
  | con pn ps, con n s =>
    if Eqb_dec pn n then args_match_unordered matches_unordered s ps else None
  | _,_ => None
end.

(*
Definition matches_unordered e pat :=
  do s <- matches_unordered_fuel (term_depth pat) e pat;
     ! e == pat[/s/]; (* since we don't check merges, we check post-hoc *)
     ret s.
 *)

Fixpoint order_subst' s args : option subst :=
  match args with
  | [] => do ret []
  | x::args' =>
    do e <- named_list_lookup_err s x;
       s' <- order_subst' s args';
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
    if Eqb_dec n n_pat then
      (* multiply depth by 2 because each level consumes 1 fuel for term
     and 1 for its args
       *)
      args_match_unordered matches_unordered s s_pat
    else None
  end.
          
(* Note that 'args' is critical to getting the order of the output subst correct.
   FV(pat) must be a permutation of args to get a result.
 *)
Definition matches (e pat : term) (args : list V) : option subst :=
  do s <- matches_unordered e pat;
     s' <- order_subst s args;
     (* this condition can fail because merge doesn't check for conflicts *)
     !term_dec e pat[/s'/];
     ret s'.


(*TODO: move to term*)
Definition sort_dec : forall x y : sort, {x = y} + {~ x = y}.
  decide equality.
  - apply (list_eq_dec term_dec).
  - apply Eqb_dec.
Defined.

Definition matches_sort t pat (args : list V) : option subst :=
  do s <- matches_unordered_sort t pat;
     s' <- order_subst s args;
     (* this condition can fail because merge doesn't check for conflicts *)
     !sort_dec t pat[/s'/];
     ret s'.

(* This lemma is pretty much trivial, but it's the useful property.
   A 'completeness' lemma is much harder, but also not as useful
   for proofs of positive statements.
*)
Lemma matches_recognizes e pat args s
  : matches e pat args = Some s ->
    e = pat[/s/].
Proof.
  unfold matches.
  (case_match;[|inversion 1]).
  (case_match;[|inversion 1]).
  (case_match;[|inversion 1]).
  symmetry in HeqH1.
  intro seq; inversion seq; subst.
  eauto.
Qed.


Lemma matches_sort_recognizes e pat args s
  : matches_sort e pat args = Some s ->
    e = pat[/s/].
Proof.
  unfold matches_sort.
  (case_match;[|inversion 1]).
  (case_match;[|inversion 1]).
  (case_match;[|inversion 1]).
  symmetry in HeqH1.
  intro seq; inversion seq; subst.
  eauto.
Qed.


Lemma order_subst_args s args s'
  : order_subst s args = Some s' ->
    args = map fst s'.
Proof.
  unfold order_subst.
  case_match;[|inversion 1].
  clear HeqH.
  revert s'.
  induction args; intro s'; simpl.
  {
    inversion 1; subst; reflexivity.
  }
  {
    case_match;[|inversion 1].
    case_match;[|inversion 1].
    inversion 1.
    simpl in *.
    f_equal.
    eauto.
  }
Qed.

Lemma matches_args e pat args s
  : matches e pat args = Some s ->
    args = map fst s.
Proof.
  unfold matches.
  case_match;[|inversion 1].
  case_match;[|inversion 1].
  case_match;[|inversion 1].
  inversion 1.
  subst.
  eapply order_subst_args.
  symmetry; eauto.
Qed.

Definition is_some {A} (x:option A) := if x then True else False.


(*TODO: move to matches or new parstep file*)
(*If the LHS of a term eq rule directly applies to e, 
  return the rule name and s such that LHS[/s/] = e.
  Rules are scanned from the root of the language.
 *)
Import OptionMonad.

Inductive step_instruction :=
| cong_instr : list (list step_instruction) -> step_instruction
| redex_instr : V -> ctx -> sort -> term -> term -> subst -> step_instruction.

(* if the top level of the term takes a step, return it *)
Fixpoint step_redex_term (l : lang) (e : term)
  : option (step_instruction * term) :=
  match l with
  | [] => None
  | (n,term_eq_rule c e1 e2 t')::l' =>
    match step_redex_term l' e with
    | Some e' => Some e'
    | None => do s <- matches e e1 (map fst c);
              ret (redex_instr n c t' e1 e2 s, e2[/s/])
    end
  | _::l' => step_redex_term l' e
  end.


(* takes steps starting from the root of the tree
   and only proceeding once the root does not reduce
*)
Fixpoint step_term_outwards_in l e : list step_instruction :=
  match step_redex_term l e with
  | Some (i,_) => [i]
  | None =>
    match e with
    | var x => []
    | con n s =>
      [cong_instr (map (step_term_outwards_in l) s)]
    end
  end.

(*TODO: following 2 fns should be merged;
cannot generate, e.g.
[beta; cong [id_right; ...]; ...]
*)
Fixpoint step_redex_term_n l e n :=
  match step_redex_term l e, n with
  | None, _ => []
  | Some (s,e'), 0 => [(s,e')]
  | Some (s,e'), S n' => (s,e')::(step_redex_term_n l e' n')
  end.

Section StepTermInner.
  Context (step_term_n : term -> list step_instruction * term)
          (l : lang).

  (*invariant: if it returns cong l,
   then l contains a nonempty list *)
  Definition step_subterm e : option (step_instruction * term) :=
    match e with
    | var x => None
    | con name s =>
    let '(arg_steps, args) := split (map step_term_n s) in
    if forallb (fun (l: list _) =>
                  if l then true else false)
               arg_steps
    then None
    else Some (cong_instr arg_steps, con name args)
    end.

  Definition step_term_one_traversal e
    : option (step_instruction * term) :=
    match step_subterm e with
    | Some p => Some p
    | None => step_redex_term l e
    end.

End StepTermInner.
      

Fixpoint step_term' l n e {struct n}
  : list step_instruction * term :=
  match n with
  | 0 => ([], e)
  | S n' =>
    match step_term_one_traversal (step_term' l n') l e with
    | Some (step,e') =>
      let '(rst_steps, e'') := (step_term' l n' e') in
      (step::rst_steps, e'')
    | None => ([], e)
    end
  end.

Definition step_term l e n := fst (step_term' l n e).


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

(*weakened form for use in reduction that has much smaller proofs*)
Inductive eq_term_nocheck l : ctx -> sort -> term -> term -> Prop :=
| eq_term_nocheck_by : forall c name t e1 e2 c' s1 s2,
    In (name,term_eq_rule c' e1 e2 t) l ->
    eq_subst l c c' s1 s2 ->
    eq_term_nocheck l c t[/s2/] e1[/s1/] e2[/s2/]
| eq_term_nocheck_cong : forall c args name t c' s1 s2,
    In (name,term_rule c' args t) l ->
    eq_args_nocheck l c c' s1 s2 ->
    eq_term_nocheck l c t[/with_names_from c' s2/] (con name s1) (con name s2)
| eq_term_nocheck_refl : forall c e t,
    eq_term_nocheck l c t e e
| eq_term_nocheck_trans : forall c t e1 e12 e2,
    eq_term_nocheck l c t e1 e12 ->
    eq_term_nocheck l c t e12 e2 ->
    eq_term_nocheck l c t e1 e2
(* Conversion:

c |- e1 = e2 : t 
               ||
c |- e1 = e2 : t'
 *)
| eq_term_nocheck_conv : forall c t t',
    eq_sort l c t t' ->
    forall e1 e2,
      eq_term_nocheck l c t e1 e2 ->
      eq_term_nocheck l c t' e1 e2
with eq_args_nocheck l : ctx -> ctx -> list term -> list term -> Prop :=
| eq_args_nocheck_nil : forall c, eq_args_nocheck l c [] [] []
| eq_args_nocheck_cons : forall c c' es1 es2,
    eq_args_nocheck l c c' es1 es2 ->
    forall name t e1 e2,
      eq_term_nocheck l c t[/with_names_from c' es2/] e1 e2 ->
      eq_args_nocheck l c ((name, t)::c') (e1::es1) (e2::es2).

  
Hint Constructors eq_term_nocheck eq_args_nocheck : lang_core.


Scheme eq_term_nocheck_ind' := Minimality for eq_term_nocheck Sort Prop
  with eq_args_nocheck_ind' := Minimality for eq_args_nocheck Sort Prop.
Combined Scheme nocheck_ind
         from eq_term_nocheck_ind', eq_args_nocheck_ind'.


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
  apply eq_args_implies_eq_subst; eauto.
  constructor.
  replace t' with t'[/id_subst c'/].
  eapply wf_term_by; basic_core_crush.
  basic_core_crush.
Qed.

Local Lemma no_check_sufficient l
  : wf_lang l ->
    (forall (c : ctx) (s : sort) (t t0 : term),
        eq_term_nocheck l c s t t0 ->
        wf_ctx l c ->
        wf_term l c t s  ->
        eq_term l c s t t0) /\
    (forall (c c0 : ctx) s s0,
        eq_args_nocheck l c c0 s s0 ->
        wf_ctx l c ->
        wf_ctx l c0 ->
        wf_args l c s c0 ->
        eq_args l c c0 s s0).
Proof.
  intro wfl.
  apply nocheck_ind.
  {
    intros.
    use_rule_in_wf.
    safe_invert H3.
    basic_core_crush.
  }
  {
    intros.
    use_rule_in_wf.
    safe_invert H4.
    remember (con name s1) as e_i.
    revert Heqe_i.
    induction H3;
      basic_goal_prep;
      basic_core_firstorder_crush.
    pose proof (in_all_fresh_same _ _ _ _ (wf_lang_ext_all_fresh wfl) H3 H) as H'.
    safe_invert H'.

    eapply eq_term_conv.
    {
      eapply eq_sort_sym.
      eapply eq_sort_subst.
      3: eapply eq_sort_refl; basic_core_crush.
      basic_core_crush.
      eapply eq_args_implies_eq_subst.
      eauto.
    }
    eapply term_con_congruence'; eauto.
  }
  solve[basic_goal_prep; basic_core_crush].
  solve[basic_goal_prep; basic_core_crush].
  solve[basic_goal_prep; basic_core_crush].
  solve[basic_goal_prep; basic_core_crush].
  {
    intros.
    safe_invert H4.
    safe_invert H5.
    constructor; basic_goal_prep; basic_core_firstorder_crush.
    apply H0.
    eapply wf_term_conv; eauto.
    eapply eq_sort_subst.
    3: eapply eq_sort_refl; basic_core_crush.
    basic_core_crush.
    eapply eq_args_implies_eq_subst.
    eauto.
  }
Qed.

Definition no_check_term l (wfl : wf_lang l) :=
  proj1 (no_check_sufficient wfl).

         
Lemma term_con_congruence_nocheck l c t name s1 s2 c' args t'
  : In (name, term_rule c' args t') l ->
    t = t'[/with_names_from c' s2/] ->
    eq_args_nocheck l c c' s1 s2 ->
    eq_term_nocheck l c t (con name s1) (con name s2).
Proof.
  intros.
  subst.
  eapply eq_term_nocheck_cong; eauto.
Qed.

Lemma eq_args_cons2_nocheck
     : forall (l : lang) (c : ctx) (s1 s2 : list term) (c' : named_list sort) 
         (name name': V) (e1 e2 e1' e2': term) (t t' : sort),
       eq_args_nocheck l c c' s1 s2 ->
       eq_term_nocheck l c t [/with_names_from c' s2 /] e1 e2 ->
       eq_term_nocheck l c t' [/with_names_from ((name,t)::c') (e2::s2) /] e1' e2'->
       eq_args_nocheck l c ((name',t')::(name, t) :: c') (e1'::e1 :: s1) (e2'::e2 :: s2) .
Proof.
  eauto with lang_core.
Qed.


Lemma eq_term_nocheck_by_with_subst name l c c' e1 e2 t s
  : In (name, term_eq_rule c' e1 e2 t) l ->
    wf_subst l c s c' ->
    eq_term_nocheck l c t [/s /] e1 [/s /] e2 [/s /].
Proof.
  intros; eapply eq_term_nocheck_by; eauto with lang_core.
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
#[export] Hint Constructors eq_term_nocheck eq_args_nocheck : lang_core.

Require Import Ltac2.Ltac2.
Import Ltac2.Message Ltac2.Control.
Set Default Proof Mode "Classic".


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
  | repeat match goal with [|- eq_args _ _ _ _ _] =>
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
  | [|-wf_subst _ _ _ _] => constructor
  | |- wf_ctx ?l ?c =>
    let c' := eval vm_compute in c in
        change_no_check (wf_ctx l c');
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
  |[|- eq_term_nocheck ?l ?ctx ?e1 ?e2 ?t] =>
   let ctx' := eval vm_compute in ctx in
       let e1' := eval vm_compute in e1 in
           let e2' := eval vm_compute in e2 in
               let t' := eval vm_compute in t in
                   change_no_check (eq_term_nocheck l ctx' e1' e2' t')
  end.

Ltac use_term_nocheck :=
  apply no_check_term;
  [ solve[prove_from_known_elabs]
  |
  | solve[repeat t']
  | solve[repeat t']].


Ltac2 rec evar_args_for c :=
  lazy_match! c with
  | _::?c' =>
    let s' := evar_args_for c' in
    open_constr:(_::$s')
  | [] => open_constr:([])
  end.

Ltac2 match_arg_evar_len () :=
  lazy_match! goal with
    [|- _ = _ [/with_names_from ?c ?s/]] =>
    let s' := evar_args_for c in
    unify $s $s'
  end.

Ltac term_cong_nocheck :=
  eapply term_con_congruence_nocheck;
  [ solve_in
  | ltac2:( match_arg_evar_len ()); vm_compute; reflexivity
  | repeat
      match goal with
      | |- eq_args_nocheck _ _ _ _ _ =>
        simple apply eq_args_nocheck_nil ||
               simple eapply eq_args_cons2_nocheck || simple eapply eq_args_nocheck_cons
      end].


Ltac2 step_redex name c' tp e1p e2p s :=
  lazy_match! goal with
  | [|- eq_term_nocheck ?l ?c _ _ _] =>
    assert (eq_term_nocheck $l $c $tp[/$s/] $e1p[/$s/] $e2p[/$s/])> [| ltac1:(eassumption)];
    apply (@eq_term_nocheck_by_with_subst $name $l $c $c' $e1p $e2p $tp $s); shelve() (*TODO: these goals are the dominating perf. bottleneck*)
  end.

Ltac2 rec step_by_instructions i :=
  (*TODO: this may need to go in a different/additional place?*)
  ltac1:(compute_eq_compilation);
  lazy_match! i with
  | cong_instr ?s =>
    (*have to run this before term_cong because for some reason
          it expects a focused goal
     *)
    let s_tac_list := List.rev (step_all_instructions s) in
    ltac1:(term_cong_nocheck);
    Control.dispatch s_tac_list
  | redex_instr ?name ?c' ?tp ?e1p ?e2p ?s =>
    step_redex name c' tp e1p e2p s
  | _ => backtrack_tactic_failure "input not an evaluated instruction"
  end
      with step_by_instructions_list l :=
    lazy_match! l with
    | [] => apply eq_term_nocheck_refl
    | ?i::?l' =>
      eapply eq_term_nocheck_trans> [step_by_instructions i |step_by_instructions_list l' ]
    | _ => backtrack_tactic_failure "input not an evaluated list"
    end
        with step_all_instructions s :=
      lazy_match! s with
      | [] => []
      | ?l::?s' => (fun () => step_by_instructions_list l)
                     ::(step_all_instructions s')
      | _ => backtrack_tactic_failure "input not an evaluated list"
      end.


Ltac2 get_step_instructions () :=
  lazy_match! goal with
  | [|- eq_term_nocheck ?l ?c' ?t ?e1 ?e2] =>
    (*TODO: 100 is a magic number; make it an input*)
    Std.eval_vm None constr:(step_term $l $e1 100)
  | [|- eq_term ?l ?c' ?t ?e1 ?e2] =>
    (*TODO: 100 is a magic number; make it an input*)
    Std.eval_vm None constr:(step_term $l $e1 100)
  | [|-_] => backtrack_tactic_failure "goal not a term equality"
  end.

(*TODO: this should now give the whole reduction
     sequence; check and if so rename *)
Ltac2 step () :=
  step_by_instructions_list (get_step_instructions ()).
Ltac2 print_steps () :=
  print (of_constr (get_step_instructions())).


Ltac lhs_concrete :=
  lazymatch goal with
  | [|- eq_term _ _ _ ?lhs _] =>
    tryif has_evar lhs then fail 0 "subject" lhs "contains evars"  else idtac
  end.

Ltac step_if_concrete := tryif lhs_concrete then use_term_nocheck;ltac2:(step()) else term_refl.


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
  eapply eq_term_trans; [ step_if_concrete | eapply eq_term_sym; step_if_concrete ].



Ltac2 get_goal_lang () :=
  lazy_match! goal with
  |[|- eq_term ?l _ _ _ _ ] => l
  end.


Ltac process_eq_term :=
  cbn -[nth_tail];
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
  cbn -[nth_tail];
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
  | |- elab_lang_ext ?pre ?l ?el => rewrite (as_nth_tail l); rewrite (as_nth_tail el)
  | _ => fail "Not a language extension wfness goal"
  end; repeat split_rule_elab;
  [apply elab_lang_nil_nth_tail; compute; reflexivity | intro.. ].


Ltac auto_elab :=
  setup_elab_lang;
  unshelve(solve [ break_elab_rule;
                   apply eq_term_refl;
                   cleanup_auto_elab ]);
  try apply eq_term_refl;
  cleanup_auto_elab.

(*TODO: duplicated; find & remove duplicates*)
Ltac unify_evar_fst_eq :=
  match goal with
  | [|- (let (x,_) := ?p in x) = ?y] =>
    let p':= open_constr:((y,_:term)) in
    unify p p';
    compute;
    reflexivity
  end.
Ltac unify_var_names s c :=
  let H' := fresh in
  assert (len_eq s c) as H';
  [ solve[repeat constructor]| clear H'];
  assert (map fst s = map fst c) as H';
  [ compute; repeat f_equal; unify_evar_fst_eq| clear H'].


Ltac eredex_steps_with lang name :=
  let mr := eval vm_compute in (named_list_lookup_err lang name) in
      lazymatch mr with
      | Some (term_eq_rule ?c ?e1p ?e2p ?tp) =>
        lazymatch goal with
        | [|- eq_term ?l ?c' ?t ?e1 ?e2] =>
          let s := open_constr:(_:subst) in
          first [unify_var_names s c | fail 100 "could not unify var names"];
          first [ replace (eq_term l c' t e1 e2)
                    with (eq_term l c' tp[/s/] e1p[/s/] e2p[/s/]);
                  [| f_equal; vm_compute; reflexivity (*TODO: is this general?*)]
                | fail 100 "could not replace with subst"];
          eapply (@eq_term_subst l c' s s c);
          [ try solve [cleanup_auto_elab]
          | eapply eq_subst_refl; try solve [cleanup_auto_elab]
          | eapply (@eq_term_by l c name tp e1p e2p); try solve [cleanup_auto_elab]]
        end
      | None =>
        fail 100 "rule not found in lang"
      end; repeat t.
