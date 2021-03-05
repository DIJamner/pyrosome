Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From Utils Require Import Utils.
From Named Require Import Exp ARule Pf PfCore PfMatches ParStep.
Import Exp.Notations Pf.Notations.

Require Import String.
Local Open Scope string.

(*TODO: move to better place *)
Fixpoint synth_term_unchecked p :=
  match p with
  | pvar x => var x
  | pcon n s => con n (map synth_term_unchecked s)
  | _ => {{e #"ERR"}}
  end.

Definition synth_sort_unchecked p :=
  match p with
  | pcon n s => scon n (map synth_term_unchecked s)
  | _ => {{s #"ERR"}}
  end.

(*TODO: "ERR" bad to have in a spec;
  really do want elab form at some point
 *)
Definition is_pf_of_le l p t1 t2 :=
  eq_pf_irr l (proj_l l p) t1
  /\ eq_pf_irr l (proj_r l p) t2.
Arguments is_pf_of_le : simpl never.

Inductive is_pf_of_wf_sort (l : pf_lang) (c :pf_ctx) : sort -> pf -> Prop :=
| elab_sort_by : forall n s es c' args,
    (n, (sort_rule_pf c' args)) \in l ->
    is_pf_of_wf_args l c s args es c' ->
    is_pf_of_wf_sort l c (scon n s) (pcon n es)
with is_pf_of_wf_term (l : pf_lang) (c :pf_ctx) : exp -> pf -> pf -> Prop :=
| elab_term_by : forall n s es c' t args,
    (n, (term_rule_pf c' args t)) \in l ->
    is_pf_of_wf_args l c s args es c' ->
    is_pf_of_wf_term l c (con n s) (pcon n es) (pf_subst (with_names_from c' es) t)
(* terms can be lifted to greater (less precise) types,
   but not the other way around; TODO: change the direction? might be more intuitive
 *)
| elab_term_conv : forall e ee p t t',
    is_pf_of_wf_term l c e ee t ->
    is_pf_of_le l p t t' ->
    is_pf_of_wf_term l c e (conv p ee) t'
| elab_term_var : forall n t,
    (n, t) \in c ->
    is_pf_of_wf_term l c (var n) (pvar n) t
with is_pf_of_wf_args (l : pf_lang) (c :pf_ctx) : list exp -> list string -> list pf -> pf_ctx -> Prop :=
| elab_args_nil : is_pf_of_wf_args l c [::] [::] [::] [::]
| elab_args_cons_ex : forall s args es c' name e ee t,
    is_pf_of_wf_term l c e ee (pf_subst (with_names_from c' es) t) ->
    (* these arguments are last so that proof search unifies existentials
       from the other arguments first*)
    is_pf_of_wf_args l c s args es c' ->
    is_pf_of_wf_args l c (e::s) (name::args) (ee::es) ((name,t)::c')
| elab_args_cons_im : forall s args es c' name ee t,
    (* no exp included *)
    is_pf_of_wf_args l c s args es c' ->
    is_pf_of_wf_args l c s args (ee::es) ((name,t)::c').

Hint Constructors is_pf_of_wf_sort is_pf_of_wf_term is_pf_of_wf_args : pfcore.


Inductive is_pf_of_wf_ctx l : ctx -> pf_ctx -> Prop :=
| elab_ctx_nil : is_pf_of_wf_ctx l [::] [::]
| elab_ctx_cons : forall name c ec v ev,
    is_pf_of_wf_ctx l c ec ->
    is_pf_of_wf_sort l ec v ev ->
    is_pf_of_wf_ctx l ((name,v)::c) ((name,ev)::ec).

Hint Constructors is_pf_of_wf_ctx : judgment.

Variant is_pf_of_wf_rule l : rule -> rule_pf -> Prop :=
| elab_sort_rule : forall c ec args,
    is_pf_of_wf_ctx l c ec ->
    subseq args (map fst ec) ->
    is_pf_of_wf_rule l (sort_rule c args) (sort_rule_pf ec args)
| elab_term_rule : forall c ec args t et,
    is_pf_of_wf_ctx l c ec ->
    is_pf_of_wf_sort l ec t et ->
    subseq args (map fst ec) ->
    is_pf_of_wf_rule l (term_rule c args t) (term_rule_pf ec args et)
| elab_le_sort_rule : forall c ec t1 et1 t2 et2,
    is_pf_of_wf_ctx l c ec ->
    is_pf_of_wf_sort l ec t1 et1 ->
    is_pf_of_wf_sort l ec t2 et2 ->
    is_pf_of_wf_rule l (sort_le c t1 t2) (sort_le_pf ec et1 et2) 
| elab_le_term_rule : forall c ec e1 ee1 e2 ee2 t et,
    is_pf_of_wf_ctx l c ec ->
    is_pf_of_wf_sort l ec t et ->
    is_pf_of_wf_term l ec e1 ee1 et ->
    is_pf_of_wf_term l ec e2 ee2 et ->
    is_pf_of_wf_rule l (term_le c e1 e2 t) (term_le_pf ec ee1 ee2 et).

Hint Constructors is_pf_of_wf_rule : pfcore.

Inductive is_pf_of_wf_lang : lang -> pf_lang -> Prop :=
| elab_lang_nil : is_pf_of_wf_lang [::] [::]
| elab_lang_cons : forall l el name r er,
    is_pf_of_wf_lang l el ->
    is_pf_of_wf_rule el r er ->
    is_pf_of_wf_lang ((name,r)::l) ((name,er)::el).

Hint Constructors is_pf_of_wf_lang : judgment.

Require Compilers.
Require Import PfCompilers.

Inductive is_pf_of_compiler (target : pf_lang)
  : Compilers.compiler -> compiler -> pf_lang -> Prop :=
| preserving_compiler_nil : is_pf_of_compiler target [::] [::] [::]
| preserving_compiler_sort : forall cmp ecmp l n c args t et,
    is_pf_of_compiler target cmp ecmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    is_pf_of_wf_sort target (compile_ctx target ecmp c) t et ->
    is_pf_of_compiler target
                             ((n, Compilers.sort_case t)::cmp)
                             ((n, et)::ecmp)
                             ((n,sort_rule_pf c args) :: l)
| preserving_compiler_term : forall cmp ecmp l n c args e ee t,
    is_pf_of_compiler target cmp ecmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    is_pf_of_wf_term target (compile_ctx target ecmp c) e ee (compile target ecmp t) ->
    is_pf_of_compiler target
                             ((n, Compilers.term_case e)::cmp)
                             ((n, ee)::ecmp)
                             ((n,term_rule_pf c args t) :: l)
| preserving_compiler_sort_le : forall cmp ecmp l n c t1 t2 p,
    is_pf_of_compiler target cmp ecmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    is_pf_of_le target p
            (compile target ecmp t1)
            (compile target ecmp t2) ->
    is_pf_of_compiler target cmp ((n,p)::ecmp) ((n,sort_le_pf c t1 t2) :: l)
| preserving_compiler_term_le : forall cmp ecmp l n c e1 e2 t p,
    is_pf_of_compiler target cmp ecmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
      is_pf_of_le target p
            (compile target ecmp e1)
            (compile target ecmp e2) ->
    is_pf_of_compiler target cmp ((n,p)::ecmp) ((n,term_le_pf c e1 e2 t) :: l).
Hint Constructors is_pf_of_compiler : pfcore.




(*TODO:move to IsPfOf*)
Definition get_rule_args_pf := 
fun r  =>
match r with
| sort_rule_pf _ args | term_rule_pf _ args _ => args
| sort_le_pf c _ _ | term_le_pf c _ _ _ => [seq i.1 | i <- c]
end.
Definition get_rule_sort r := 
match r with
| sort_rule_pf _ _
| sort_le_pf _ _ _ => pcon "ERR" [::]
| term_rule_pf _ _ t
| term_le_pf _ _ _ t => t
end.

Lemma elab_sort_by' (l : pf_lang) c : forall n s es,
    let r := named_list_lookup (sort_rule_pf [::] [::]) l n in
    let args := get_rule_args_pf r in
    let c' := get_rule_ctx r in
    (n, (sort_rule_pf c' args)) \in l ->
    is_pf_of_wf_args l c s args es c' ->
    is_pf_of_wf_sort l c (scon n s) (pcon n es).
Proof.
  eauto with pfcore.
Qed.

Lemma elab_term_by' l c : forall n s es t,
    let r := named_list_lookup (sort_rule_pf [::] [::]) l n in
    let args := get_rule_args_pf r in
    let c' := get_rule_ctx r in
    let t' := get_rule_sort r in
    (n, (term_rule_pf c' args t')) \in l ->
    is_pf_of_wf_args l c s args es c' ->
    t = (pf_subst (with_names_from c' es) t') ->
    is_pf_of_wf_term l c (con n s) (pcon n es) t.
Proof.
  intros; subst;
  eauto with pfcore.
Qed.

Ltac break_is_pf_of_wf_args :=
  cbn;
  repeat lazymatch goal with
    | [|- is_pf_of_wf_args _ _ _ (?n::_) _ ((?n,_)::_)] =>
      eapply elab_args_cons_ex
    | [|- is_pf_of_wf_args _ _ _ _ _ ((?n,_)::_)] =>
      eapply elab_args_cons_im
    | [|- is_pf_of_wf_args _ _ _ _ _ [::]] =>
      eapply elab_args_nil
    end.

Ltac solve_sort_equality :=
  compute;
  match goal with
    [|- ?t1 = ?t2] =>
    reflexivity ||
    fail "sort" t1 "is not unifiable with sort" t2
  end.
  
Ltac pcon :=
  lazymatch goal with
  | [|-is_pf_of_wf_sort ?l ?c ?t ?pt] =>
    let t' := eval compute in t in
    let pt' := eval compute in pt in
    (* should never succeed:
       assert_fails (is_evar t'; is_evar pt'); *)
    let c' := eval compute in c in
    change_no_check (is_pf_of_wf_sort l c' t' pt');
    eapply elab_sort_by'; [ by compute|break_is_pf_of_wf_args]
  | [|-is_pf_of_wf_term ?l ?c ?e ?pe ?t] =>
    let e' := eval compute in e in
    let pe' := eval compute in pe in
    (* should never succeed:
       assert_fails (is_evar e'; is_evar pe'); *)
    let c' := eval compute in c in
    let t' := eval compute in t in
    change_no_check (is_pf_of_wf_term l c' e' pe' t');
    eapply elab_term_by'; [ by compute| break_is_pf_of_wf_args | solve_sort_equality]
  end.

(*TODO something funny w/ printed evars in error; 
  maybe a backtracking thing?
*)
Ltac pvar :=
  eapply elab_term_var;
      apply named_list_lookup_err_in;
      match goal with
        [|- Some ?t = named_list_lookup_err ?c ?x] =>
        let t' := eval compute in t in
        let t_r := eval compute in (named_list_lookup_err c x) in
        change_no_check (Some t' = t_r);
        compute;
        reflexivity ||
        fail "attempted to use var" x "at type" t'
        "when it has type" t_r
      end.

(*TODO: move to the right place*)
Lemma is_pf_of_le_trans l p1 p2 t1 t12 t2
  : is_pf_of_le l p1 t1 t12 ->
    is_pf_of_le l p2 t12 t2 ->
    is_pf_of_le l (trans p1 p2) t1 t2.
Proof.
  unfold is_pf_of_le.
  cbn [proj_l proj_r].
  easy.
Qed.


Lemma is_pf_of_le_sym l p t1 t2
  : is_pf_of_le l p t1 t2 ->
    is_pf_of_le l (sym p) t2 t1.
Proof.
  unfold is_pf_of_le.
  cbn [proj_l proj_r].
  easy.
Qed.


Lemma is_pf_of_le_refl l t
  : is_exp t -> is_pf_of_le l t t t.
Proof.
Admitted.

  (*rewrite from left to right*)
    Require Import RuleStep.

    Ltac solve_one_rule_left_to_right_lhs rule_name :=
    lazymatch goal with
      [|- is_pf_of_le ?l ?p_evar ?lhs ?rhs] =>
      tryif is_evar rhs; is_evar p_evar
      then
        let x := eval compute in (rule_step_left l rule_name lhs) in
            lazymatch x with
            | Some ?p =>
              let rhs' := eval compute in (proj_r l p) in
              unify p_evar p;
              unify rhs' rhs;
              by compute
            | None => fail "rule" rule_name
                           "could not be rewritten from left to right in" lhs
            end
      else fail "rhs and p_evar not evars"
    end.

    (*TODO: reduce code duplication *)
    Ltac solve_one_rule_right_to_left_rhs rule_name :=
    lazymatch goal with
      [|- is_pf_of_le ?l ?p_evar ?lhs ?rhs] =>
      tryif is_evar lhs; is_evar p_evar
      then
        let x := eval compute in (rule_step_right l rule_name rhs) in
            lazymatch x with
            | Some ?p =>
              let lhs' := eval compute in (proj_l l p) in
              unify p_evar p;
              unify lhs' lhs;
              by compute
            | None => fail "rule" rule_name
                           "could not be rewritten from right to left in" rhs
            end
      else fail "lhs and p_evar not evars"
      end.

(*TODO: get better errors on these*)
Ltac le_rewrite rule_name :=
  first [ eapply is_pf_of_le_trans;
          [solve_one_rule_left_to_right_lhs rule_name |]
        | eapply is_pf_of_le_trans;
          [| eapply is_pf_of_le_sym;
             solve_one_rule_right_to_left_rhs rule_name]].

Ltac le_rewrite_rtl rule_name :=
  first [ eapply is_pf_of_le_trans;
          [eapply is_pf_of_le_sym;
           solve_one_rule_right_to_left_rhs rule_name |]
        | eapply is_pf_of_le_trans;
          [|solve_one_rule_left_to_right_lhs rule_name]].

Ltac le_reflexivity :=
      apply is_pf_of_le_refl; apply /check_is_expP; by compute.

Ltac reduce fuel :=
  lazymatch goal with
    [|- is_pf_of_le ?l ?p_evar ?lhs ?rhs] =>
    tryif is_evar p_evar
    then
      let lhsp := eval compute in (par_step_n l lhs fuel) in
          let rhsp := eval compute in (par_step_n l rhs fuel) in
              let lhs' := eval compute in (proj_r l lhsp) in
                  let rhs' := eval compute in (proj_r l rhsp) in
                      let p_r := open_constr:(trans _ (sym rhsp)) in
                      apply (@is_pf_of_le_trans l lhsp p_r lhs lhs' rhs);
                      [by compute |];
                      apply (is_pf_of_le_trans (t12 := rhs'));
                      [| by compute]
    else fail p_evar "not an evar"
  end.

Local Open Scope string.
