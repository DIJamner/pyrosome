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
From Named Require Import Core Elab.
Import Core.Notations.
Import OptionMonad.

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
  Context (matches_unordered : forall (e pat : exp), option subst).
  Fixpoint args_match_unordered (s pat : list exp) : option subst :=
       match pat, s with
       | [],[] => do ret []
       | pe::pat',e::s' =>
         do res_e <- matches_unordered e pe;
            res_s <- args_match_unordered s' pat';
            ret (unordered_merge_unsafe res_e res_s)                          
       | _,_ => None
       end.
End InnerLoop.

(* TODO: move to exp*)
Fixpoint exp_dec (x y : exp) {struct x} : {x = y} + {~ x = y}.
  refine (match x,y with
          | var n, var m => if string_dec n m then left _ else right _
          | con n s, con n' s' =>
            if string_dec n n'
            then if list_eq_dec exp_dec s s' then left _ else right _
            else right _
          | _, _ => right _
          end).
  all: try let H := fresh in intro H; inversion H; clear H; subst.
  all: basic_exp_crush.
Defined.

(* Finds the subst s such that s >= acc, e = pat[/s/]
   and (map fst s) = FV(e) U (map fst acc), if such a substitution exists.
   Behavior intentionally unspecified otherwise.
*)
Fixpoint matches_unordered (e pat : exp) : option subst :=
  match pat, e with
  | var px, _ => Some ([(px,e)])
  | con pn ps, con n s =>
    if string_dec pn n then args_match_unordered matches_unordered s ps else None
  | _,_ => None
end.

(*
Definition matches_unordered e pat :=
  do s <- matches_unordered_fuel (exp_depth pat) e pat;
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

(*
Lemma order_subst'_vals s args s' p
  : all_fresh s ->
    order_subst' s args = Some s' ->
    p \in s ->
    p.1 \in args ->
    p \in s'.             
Proof.
  simpl in *.
  ltac1:(break); simpl.
  revert s'.
  induction args; intro s'; simpl.
  {    
    intros _ _ _ absurd; inversion absurd.
  }
  {
    intro.
    ltac1:(case_match;[|inversion]).
    ltac1:(case_match;[|inversion]).
    intro s'eq; inversion s'eq; clear s'eq; subst.
    rewrite !in_cons.
    intro.
    ltac1:(move /orP; case).
    {
      ltac1:(move /eqP); intro s0eq; subst.
      (*Lemma lookup_in
       *)
Admitted.
*)

Definition order_subst s args :=
  (*guarantees that args is a permutation of (map fst s)
    if this function returns a result.
   *)
  if Nat.eqb (length s) (length args) then order_subst' s args else None.

(*
Lemma order_subst_vals s args s' p
  : all_fresh s ->
    order_subst s args = Some s' ->
    p \in s ->
    p.1 \in args ->
    p \in s'.             
Proof.
  intro.
  unfold order_subst.
  ltac1:(case_match;[|inversion]).
  eauto using order_subst'_vals.
Qed.
*)

(*
Lemma matches_unordered_fuel_all_fresh e pat fuel s
  : matches_unordered_fuel fuel e pat = Some s ->
    all_fresh s.
Proof.
  unfold matches_unordered.
*)

(*
Lemma matches_unordered_all_fresh e pat s
  : matches_unordered e pat = Some s ->
    all_fresh s.
Proof.
  unfold matches_unordered.
  *)

Definition matches_unordered_sort (t pat : sort) :=
  match t, pat with
  | scon n s, scon n_pat s_pat =>
    if string_dec n n_pat then
      (* multiply depth by 2 because each level consumes 1 fuel for exp
     and 1 for its args
       *)
      args_match_unordered matches_unordered s s_pat
    else None
  end.
          
(* Note that 'args' is critical to getting the order of the output subst correct.
   FV(pat) must be a permutation of args to get a result.
 *)
Definition matches (e pat : exp) (args : list string) : option subst :=
  do s <- matches_unordered e pat;
     s' <- order_subst s args;
     (* this condition can fail because merge doesn't check for conflicts *)
     !exp_dec e pat[/s'/];
     ret s'.


(*TODO: move to exp*)
Definition sort_dec : forall x y : sort, {x = y} + {~ x = y}.
  decide equality.
  - apply (list_eq_dec exp_dec).
  - apply string_dec.
Defined.

Definition matches_sort t pat (args : list string) : option subst :=
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
Goal
  (let e:= con "foo" [ con "quox" []; con "bar" [ con "baz"[]]; var "b"]in
   is_some (matches e  (con "foo" [ con "quox" []; var "b"; var "a"]) ["b";"a"])).
  vm_compute; exact I.
Qed.


(*TODO: move to matches or new parstep file*)
(*If the LHS of a term eq rule directly applies to e, 
  return the rule name and s such that LHS[/s/] = e.
  Rules are scanned from the root of the language.
 *)
Import OptionMonad.

Inductive step_instruction :=
| cong_instr : list step_instruction -> step_instruction
| refl_instr : step_instruction
| redex_instr : string -> ctx -> sort -> exp -> exp -> subst -> step_instruction.

Fixpoint step_redex_term (l : lang) (e : exp) : option step_instruction :=
  match l with
  | [] => None
  | (n,term_eq_rule c e1 e2 t')::l' =>
    match step_redex_term l' e with
    | Some e' => Some e'
    | None => do s <- matches e e1 (map fst c);
              ret (redex_instr n c t' e1 e2 s)
    end
  | _::l' => step_redex_term l' e
  end.


Inductive wf_term_no_conv l : ctx -> exp -> sort -> Prop :=
  | wf_term_by_no_conv : forall c n s args c' t,
      In (n, term_rule c' args t) l ->
      wf_args l c s c' ->
      wf_term_no_conv l c (con n s) t[/(with_names_from c' s)/]
  | wf_term_var_no_conv : forall c n t,
      In (n, t) c ->
      wf_term_no_conv l c (var n) t.
Local Hint Constructors wf_term_no_conv : lang_core.

Lemma wf_term_peel_convs l c e t
  : wf_term l c e t -> exists t', wf_term_no_conv l c e t'.
Proof.
  induction 1; basic_core_crush.
Qed.




Fixpoint step_term l e : option step_instruction :=
  match step_redex_term l e with
  | Some i => Some i
  | None =>
    match e with
    | var x => Some refl_instr
    | con n s =>
      option_map cong_instr (Mmap (step_term l) s)
    end
  end.


Require Import Ltac2.Ltac2.
Import Ltac2.Message Ltac2.Control.
Set Default Proof Mode "Classic".

Lemma wf_args_cons2
     : forall (l : lang) (c : ctx) (s : list exp) (c' : named_list sort) 
         (name name': string) (e e': exp) (t t' : sort),
       wf_term l c e t [/with_names_from c' s /] ->
       wf_term l c e' t' [/with_names_from ((name,t)::c') (e::s) /] ->
       wf_args l c s c' -> wf_args l c (e'::e :: s) ((name',t')::(name, t) :: c').
Proof.
  eauto with lang_core.
Qed.

Lemma eq_args_cons2
     : forall (l : lang) (c : ctx) (s1 s2 : list exp) (c' : named_list sort) 
         (name name': string) (e1 e2 e1' e2': exp) (t t' : sort),
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


Ltac solve_in := apply named_list_lookup_err_in; compute; reflexivity.

Ltac lookup_wf_lang := assumption (*TODO: add to ctx beforehand, use assumption here*).


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

Ltac solve_len_eq := solve[ repeat constructor].

Ltac term_cong :=
  eapply term_con_congruence;
  [ solve_in
  | solve_len_eq
  | compute; reflexivity
  | lookup_wf_lang
  | repeat match goal with [|- eq_args _ _ _ _ _] =>
                           simple apply eq_args_nil
                           || simple eapply eq_args_cons2
                           || simple eapply eq_args_cons
           end].
Ltac term_refl := 
  apply eq_term_refl; shelve (*TODO: solve[repeat t']*).


Ltac eq_term_by s := 
  eapply (eq_term_by _ _ s); solve_in.

(*TODO: optimize where this is used so that I don't
  duplicate work?
*)
Local Ltac t' :=
  match goal with
  | [|- fresh _ _ ]=> apply use_compute_fresh; compute; reflexivity
  | [|- sublist _ _ ]=> apply (use_compute_sublist string_dec); compute; reflexivity
  | [|- In _ _ ]=> solve_in
  | [|- wf_term _ _ _ _] => assumption || eapply wf_term_var || eapply wf_term_by'
  | [|-wf_args _ _ _ _] => simple apply wf_args_nil
                           || simple eapply wf_args_cons2
                           || simple eapply wf_args_cons
  | [|-wf_subst _ _ _ _] => constructor
  | [|-wf_ctx _ _] => assumption || constructor
  | [|- wf_sort _ _ _] => eapply wf_sort_by
  | [|- wf_lang _] => lookup_wf_lang
  | [|- _ = _] => compute; reflexivity
  end.

  Local Ltac t :=
  match goal with
  | [|- fresh _ _ ]=> apply use_compute_fresh; compute; reflexivity
  | [|- sublist _ _ ]=> apply (use_compute_sublist string_dec); compute; reflexivity
  | [|- In _ _ ]=> apply named_list_lookup_err_in; compute; reflexivity
  | [|- len_eq _ _] => econstructor
  | [|-elab_sort _ _ _ _] => eapply elab_sort_by
  | [|-elab_ctx _ _ _] => econstructor
  | [|-elab_args _ _ _ _ _ _] => eapply elab_args_cons_ex' || econstructor
  | [|-elab_term _ _ _ _ _] => eapply elab_term_var || eapply elab_term_by'
  | [|-wf_term _ _ _ _] => shelve
  | [|-elab_rule _ _ _] => econstructor
  | [|- _ = _] => compute; reflexivity
  end.

    
    (*TODO: only works if all variables appear on the lhs*)
    Ltac redex_steps_with lang name :=
    let mr := eval compute in (named_list_lookup_err lang name) in
    lazymatch mr with
    | Some (term_eq_rule ?c ?e1p ?e2p ?tp) =>
      lazymatch goal with
      | [|- eq_term ?l ?c' ?t ?e1 ?e2] =>
        let ms := eval compute in (matches e1 e1p (map fst c)) in
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

    Ltac2 step_redex name c' tp e1p e2p s :=
        lazy_match! goal with
        | [|- eq_term ?l ?c _ _ _] =>
          assert (eq_term $l $c $tp[/$s/] $e1p[/$s/] $e2p[/$s/])> [| ltac1:(eassumption)];
          apply (@eq_term_by_with_subst $name $l $c $c' $e1p $e2p $tp $s); solve [repeat ltac1:(t')]
        end.

    Ltac2 get_goal_lang () :=
      lazy_match! goal with
      |[|- eq_term ?l _ _ _ _ ] => l
      end.

    Ltac2 rec step_by_instructions i :=
      lazy_match! i with
      | refl_instr => ltac1:(term_refl)
      | cong_instr ?s =>
        (*have to run this before term_cong because for some reason
          it expects a focussed goal
         *)
        let s_tac_list := List.rev (step_all_instructions s) in
        ltac1:(term_cong);
        Control.dispatch s_tac_list
      | redex_instr ?name ?c' ?tp ?e1p ?e2p ?s =>
        step_redex name c' tp e1p e2p s
      | _ => backtrack_tactic_failure "input not an evaluated instruction"
    end
    with step_all_instructions s :=
      lazy_match! s with
      | [] => []
      | ?i::?s' => (fun () => step_by_instructions i)::(step_all_instructions s')
      | _ => backtrack_tactic_failure "input not an evaluated list"
      end.

    Ltac2 get_step_instructions () :=
    lazy_match! goal with
     | [|- eq_term ?l ?c' ?t ?e1 ?e2] =>
       let mi := Std.eval_vm None constr:(step_term $l $e1) in
       lazy_match! mi with
       | Some ?i => i
       | None =>  backtrack_tactic_failure "could not generate step instructions"
       end
     | [|-_] => backtrack_tactic_failure "goal not a term equality"
  end.
      
    Ltac2 step () :=
      step_by_instructions (get_step_instructions ()).
    Ltac2 print_steps () :=
      print (of_constr (get_step_instructions())).

  Ltac compute_eq_compilation :=
    match goal with
    |[|- eq_sort ?l ?ctx ?t1 ?t2] =>
     let ctx' := eval compute in ctx in
     let t1' := eval compute in t1 in
     let t2' := eval compute in t2 in
     change (eq_sort l ctx' t1' t2')
    |[|- eq_term ?l ?ctx ?e1 ?e2 ?t] =>
     let ctx' := eval compute in ctx in
     let e1' := eval compute in e1 in
     let e2' := eval compute in e2 in
     let t' := eval compute in t in
     change (eq_term l ctx' e1' e2' t')
    end.

    
    Ltac reduce :=
      repeat (eapply eq_term_trans; [ltac2:(step())|compute_eq_compilation]);
      term_refl.
    Ltac by_reduction :=
      eapply eq_term_trans; [reduce | eapply eq_term_sym; reduce].






(* TODO: something like this is necessary for
   a reflective stepper. 
   The only other option is for the stepper to
   out put a list of side-conditions

Lemma subst_wf_injective l c s
  : wf_lang l ->
    all_fresh s ->
    (forall c' t',
        wf_sort l c' t' ->
          wf_sort l c t'[/s/] ->
          set_eq (map fst s) (fv_sort t') ->
          map fst s = map fst c' ->
          wf_subst l c s c') /\
    (forall c' e' t',
        wf_term l c' e' t' ->
        forall t,
          wf_term l c e'[/s/] t ->
          set_eq (map fst s) (fv e') ->
          map fst s = map fst c' ->
          (*wf_term l c e  t'[/s/] /\*)  wf_subst l c s c') /\
    (forall c' s1 c1,
        wf_args l c' s1 c1 ->
        forall c2,
          wf_args l c s1[/s/] c2 ->
          set_eq (map fst s) (fv_args s1) ->
          map fst s = map fst c' ->
          wf_subst l c s c').
Proof.
  intros wfl allfs.
  apply wf_judge_ind.
  {
    intro_to wf_sort.
    inversion 1; basic_goal_prep;
      basic_core_crush.
  }
  (*
    pose proof (in_all_fresh_same _ _ _ _ (wf_lang_all_fresh wfl) H H6).
    basic_core_crush. *)
  {
    intro_to wf_term.
    intro wft.
    apply wf_term_peel_convs in wft.
    destruct wft as [t' wft].
    safe_invert wft.
    basic_goal_prep.
    pose proof (in_all_fresh_same _ _ _ _ (wf_lang_all_fresh wfl)  H H5).
    safe_invert H4; eauto.
  }
  {
    firstorder.
  }
  {
    destruct s; basic_goal_prep.
    {
      destruct c0; basic_goal_prep;
        basic_utils_crush.
    }
    {
      assert (s=[]) by 
          admit (*incl and all_fresh*).
      subst; basic_goal_prep.
      assert (s0 = n) by admit (*set_eq*).
      subst.
      rewrite eqb_refl in H0.
      destruct c0; basic_goal_prep.
      basic_utils_crush.
      safe_invert H2; subst.
      destruct c0; basic_goal_prep.
      2:basic_utils_crush.
      constructor.
      constructor.
      
      admit (*incl and all_fresh*).
    basic_core_crush.
    destruct s; basic_goal_prep;
      basic_core_crush.
    destruct c0; basic_goal_prep;
      basic_utils_crush.
    destruct c0; basic_goal_prep;
      basic_core_crush.
    
    
    
    exfalso.
    clear H2 H5 H4 H0 H t t0 c0.
    unfold incl in *
    simpl in
    todo: list-set math
*)
