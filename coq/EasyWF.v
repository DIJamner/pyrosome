(*********************************************
A partial recognizer for well-formed languages
**********************************************)


Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(* TODO: change from loads to imports *)
From excomp Require Import Utils Exp Rule CoreDefs Core.


Fixpoint lookup_rule n l m : option rule :=
  match l, m with
  | [::], _ => None
  | r'::l', 0 => Some r'%%!n.+1
  |  _::l', m'.+1 =>
     lookup_rule n.+1 l' m'
  end.

Lemma lookup_result_shifted n l m r :  lookup_rule n l m = Some r -> exists r', r = r'%%!n.
Proof.
  elim: l n m => //=.
  intros until m; case: m => //=.
  - case => <-.
    change (n.+1) with (1+n).
    rewrite -rule_constr_shift_shift.
    eauto.
  - move => m /H.
    case => r' ->.
    change (n.+1) with (1+n).
    rewrite -rule_constr_shift_shift.
    eauto.
Qed.    

Lemma lookup_rule_is_nth n l m r : lookup_rule n l m = Some r%%!n -> Is_Nth r l m.
Proof.
  elim: l r m n => //=.
  intros until m.
  case: m => //=.
  - move => n.
    case.
    change (n.+1) with (1+n).
    rewrite -rule_constr_shift_shift.
    move /rule_constr_shift_inj => req.
    move: req H => <- H.
    clear r.
    constructor.
  - move => m n lu.
    apply /is_nthP; simpl.
    case rcd: (rule_constr_downshift 1 r).
    1:{
      apply /is_nthP.
      symmetry in rcd.
      move: rcd lu => /rule_downshift_inj <-.
      clear r.
      rewrite rule_constr_shift_shift.
      change (1+n) with (n.+1).
        by move /H.
    }
    1:{
      move: lu rcd.
      move /lookup_result_shifted.
      case => r'.
    change (n.+1) with (1+n).
    rewrite -rule_constr_shift_shift.
    move /rule_constr_shift_inj ->.
      by rewrite rule_downshift_left_inverse.
    }
Qed.

Lemma lookup_rule_is_nth' l m r : lookup_rule 0 l m = Some r -> Is_Nth r l m.
Proof.
  rewrite -{1}(rule_constr_shift_0_id r).
  apply: lookup_rule_is_nth.
Qed.
  
Definition lookup_sort_args l n : option ctx :=
  match lookup_rule 0 l n with
  | Some ({| c |- sort}) => Some c
  | _ => None
  end.
Hint Unfold lookup_sort_args.
Hint Transparent lookup_sort_args.

Definition lookup_term_args l n : option ctx :=
  match lookup_rule 0 l n with
  | Some ({| c |- _}) => Some c
  | _ => None
  end.
Hint Unfold lookup_term_args.
Hint Transparent lookup_term_args.

Definition lookup_term_sort l n : option exp :=
  match lookup_rule 0 l n with
  | Some ({| _ |- t}) => Some t
  | _ => None
  end.
Hint Unfold lookup_term_sort.
Hint Transparent lookup_term_sort.


Notation "@@[ default ] fuel =1> fuel' ; e @@" :=
  (match fuel with
     | 0 => default
     | fuel'.+1 => e
     end).

Fixpoint is_easy_wf_sort l c t fuel : bool :=
  @@[false] fuel =1> fuel';
    match t with
    | var x => false
    | con n s =>
      match lookup_sort_args l n with
      | Some c' => is_easy_wf_subst l c s c' fuel'
      | None => false
      end
    end@@
with is_easy_wf_subst l c s c' fuel : bool :=
       @@[false] fuel =1> fuel';
         match s, c' with
         | [::], [::] => is_easy_wf_ctx l c fuel'
         | e::s', t::c'' =>
           is_easy_wf_term l c e t[/s' /] fuel'
           && is_easy_wf_subst l c s' c'' fuel'
         | _, _ => false
         end@@
with is_easy_wf_term l (c : ctx) e t fuel : bool :=
       @@[false] fuel =1> fuel';
         match e with
         | var x =>
           match List.nth_error c x with
           | Some t' => is_easy_wf_ctx l c fuel' && (t == t') (*TODO: use le judgment*)
           | None => false
           end
         | con n s => false (*TODO*)
         end@@
with is_easy_wf_ctx l c fuel : bool :=
       @@[false] fuel =1> fuel';
         match c with
         | [::] => is_easy_wf_lang l fuel'
         | t::c' =>
           is_easy_wf_sort l c' t fuel'
           && is_easy_wf_ctx l c' fuel'
         end@@
with is_easy_wf_lang l fuel : bool :=
       @@[false] fuel =1> fuel';
         match l with
         | [::] => true
         | r::l' => 
           is_easy_wf_rule l' r fuel'
           && is_easy_wf_lang l' fuel'
         end@@
with is_easy_wf_rule l r fuel : bool :=
       @@[false] fuel =1> fuel';
         match r with
         | {| c |- sort } => is_easy_wf_ctx l c fuel'
         | {| c |- t } => is_easy_wf_sort l c t fuel'
         | {< c1 <# c2 |- t1 <# t2 } => false
         | {< c1 <# c2 |- e1 <# e2 .: t1 <# t2 } => false
         end@@.

Ltac exp_head e :=
  match e with
  | ?e' _ => exp_head e'
  | ?e' => e
  end.


Ltac match_arg_head hd t :=
  match t with
  | context [hd] => idtac
  | _ => fail "did not match head" hd "to an input type of" t
  end.

Ltac view_is_easy_IH_and_intro :=
  match goal with
  | |- ?A -> _ =>
    let Ahd := exp_head A in
    match goal with
    | H : ?T |-_=>
      match_arg_head Ahd T;
        let wfx := fresh "wf" in
        move /H => wfx
    end
  end.

Unset SsrIdents.

Ltac solve_easy_wf_from_hyps :=
  repeat first [ case /andP
          | view_is_easy_IH_and_intro
          | intro ];
  by eauto.

Theorem is_easy_wf_recognizes fuel
  : (forall l, is_easy_wf_lang l fuel -> wf_lang l)
    /\ (forall l r, is_easy_wf_rule l r fuel -> wf_rule l r)
    /\ (forall l c, is_easy_wf_ctx l c fuel -> wf_ctx l c)
    /\ (forall l c t, is_easy_wf_sort l c t fuel -> wf_sort l c t)
    /\ (forall l c s c', is_easy_wf_subst l c s c' fuel -> wf_subst l c s c')
    /\ (forall l c e t, is_easy_wf_term l c e t fuel -> wf_term l c e t).
Proof.
  elim: fuel => //=.
  move => fuel.
  case => [IHlang [IHrule [IHctx [IHsort [IHsubst IHterm]]]]].
  split.
  1:{
    case; auto.
    solve_easy_wf_from_hyps.
  }
  split.
  1:{
    move => l.
    case; auto.
  }
  split.
  1:{
    move => l.
    case; auto.
    solve_easy_wf_from_hyps.
  }
  split.
  1:{
    move => l c.
    case => //=.
    move => n s.
    unfold lookup_sort_args.
    case lsa: (lookup_rule 0 l n) => //=.
    case: _a_ lsa => //=.
    move => c' /lookup_rule_is_nth' => isn.
    solve_easy_wf_from_hyps.
  }
  split.
  1:{
    move => l c.
    case => //=.
    case => //=; by eauto.
    move => e s.
    case => //=.
    solve_easy_wf_from_hyps.
  }
  1:{
    move => l c.
    case => //=.
    move => n t.
    case lne: (List.nth_error c n) =>//=.
  repeat first [ case /andP
          | view_is_easy_IH_and_intro
          | intro ].
  constructor; eauto.
  move: b => /eqP -> => //.
  }
Qed.

(* Tactics for using the partial recognizer to prove a language well-formed *)
(*TODO: generalize to all constructs, not just langs*)
Ltac solve_easy_wf_lang n :=
  suff: is_easy_wf_lang cat_stx n;
  [ intros; eapply is_easy_wf_recognizes; by eauto
  | by compute].

Tactic Notation "solve_easy_wf_lang" constr(n) := solve_easy_wf_lang n.
Tactic Notation "solve_easy_wf_lang" := solve_easy_wf_lang 1000.
    
(*  
  Ltac case_matched_or_intro :=
    match goal with
      |- forall x, _ =>
      intro x;
      match goal with
      | |- context [match x with | var _ => _ | con n s => _  end] => case
      | _ => idtac
      end
    end.
  
  case_matched_or_intro.
  case_matched_or_intro.
  case_matched_or_intro.
  case_matched_or_intro.
  case_matched_or_intro.
  
  Ltac match_arg_head hd t :=
    match t with
    | forall x, ?t' => match_arg_head t'
    | ?e -> ?t' =>
      let eh := exp_head e in
      constr_eq_strict eh hd
      || match_arg_head hd t'
    | _ => fail hd "did not match an input type head of" t
    end.

Ltac get_is_easy_IH hd :=
  match goal with
  | H :  |- _

Ltac view_with_is_easy_IH :=
  match goal with
  | |- ?E -> _ =>
    let exp_head 
*)
