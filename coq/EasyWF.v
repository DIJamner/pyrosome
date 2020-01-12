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

Notation "x <-[ default ] val ; body" :=
  (match val with
   | Some x => body
   | None => default
   end) (at level 80, right associativity).

Require Import String.

(* Give good error messages so that users know what goes wrong
   Note: an error does not mean the term is necessarily ill-formed
   just that more fuel will not change the result
 *)
Variant wf_result : Set :=
| wf_success
| wf_no_fuel
| wf_error (s : string).

Definition wf_result_is_success r : bool :=
  match r with
  | wf_success => true
  | _ => false
  end.

Coercion wf_result_is_success : wf_result >-> bool.

Definition wf_result_seq r1 : wf_result -> wf_result :=
  match r1 with
  | wf_success => id
  | _ => fun _ => r1
  end.

Notation "check! r1 ; r2" := (wf_result_seq r1 r2) (at level 80, right associativity).

Notation "check![ es ] b1 ; r" :=
  (wf_result_seq (if b1 then wf_success else wf_error es) r)
    (at level 80, right associativity).

Fixpoint is_easy_wf_sort fuel :=
  @@[fun l c t => wf_no_fuel] fuel =1> fuel';
    fun l c t =>
    match t with
    | var x => wf_error "Variables are not valid sorts"
    | con n s =>
      c' <-[wf_error "Sort rule out of bounds"] lookup_sort_args l n;
      is_easy_wf_subst fuel' l c s c'
    end@@
with is_easy_wf_subst fuel : lang -> ctx -> subst -> ctx -> wf_result :=
       @@[fun l c s c' => wf_no_fuel] fuel =1> fuel';
         fun l c s c' => match s, c' with
         | [::], [::] => is_easy_wf_ctx fuel' l c
         | e::s', t::c'' =>
           check! is_easy_wf_term fuel' l c e t[/s' /];
             is_easy_wf_subst fuel' l c s' c''
         | _, _ => wf_error "Substitution and output context of different lengths"
         end@@
with is_easy_wf_term fuel : lang -> ctx -> exp -> exp -> wf_result :=
       @@[fun l c e t => wf_no_fuel] fuel =1> fuel';
         fun l c e t => match e with
         | var x =>
           t' <-[wf_error "Term variable out of bounds"] List.nth_error c x;
           check!["Variable type mismatch"] t == t';
           is_easy_wf_ctx fuel' l c
           (*TODO: get this to work && is_easy_le_sort l c c t' t fuel'*)
         | con n s =>
           c' <-[wf_error "Term constructor out of bounds"] lookup_term_args l n;
           t' <-[wf_error "Term constructor out of bounds"] lookup_term_sort l n;
           check!["Constructor type mismatch"] t'[/s/] == t;
           is_easy_wf_subst fuel' l c s c'
         end@@
with is_easy_wf_ctx fuel : lang -> ctx -> wf_result :=
       @@[fun l c => wf_no_fuel] fuel =1> fuel';
         fun l c => match c with
         | [::] => wf_success
         | t::c' =>
           check! is_easy_wf_sort fuel' l c' t;
           is_easy_wf_ctx fuel' l c'
         end@@.
Fixpoint is_easy_wf_lang fuel : lang -> bool :=
       @@[fun l => false] fuel =1> fuel';
         fun l => match l with
         | [::] => true
         | r::l' => is_easy_wf_rule fuel' l' r
                    && is_easy_wf_lang fuel' l'
         end@@
with is_easy_wf_rule fuel :=
       @@[fun l r => false] fuel =1> fuel';
         fun l r => match r with
         | {| c |- sort } => is_easy_wf_ctx fuel' l c
         | {| c |- t } => is_easy_wf_sort fuel' l c t
         | {< c1 <# c2 |- t1 <# t2 } =>
           (is_easy_le_ctx l c1 c2 fuel')
             && (is_easy_wf_sort fuel' l c1 t1)
             && (is_easy_wf_sort fuel' l c2 t2)
         | {< c1 <# c2 |- e1 <# e2 .: t1 <# t2 } =>
           (is_easy_le_sort l c1 c2 t1 t2 fuel')
             && (is_easy_wf_term fuel' l c1 e1 t1)
             && (is_easy_wf_term fuel' l c2 e2 t2)
         end@@
with is_easy_le_sort l (c1 c2 : ctx) (t1 t2 : exp) fuel : bool :=
  @@[false] fuel =1> fuel';
    (*refl*) ((c1 == c2) && (t1 == t2) && is_easy_wf_sort fuel' l c1 t1)
    || (* by *) (is_easy_wf_lang fuel' l && rule_in ({<c1 <# c2 |- t1 <# t2}) l)
    (*TODO: trans, subst (these are the scary cases performance-wise)*)
    @@
with is_easy_le_ctx l (c1 c2 : ctx) fuel : bool :=
       @@[false] fuel =1> fuel';
       match c1, c2 with
       | [::],[::] => is_easy_wf_lang fuel' l
       | t1::c1',t2::c2' => is_easy_le_sort l c1' c2' t1 t2 fuel'
       | _, _ => false
       end@@.


Definition is_easy_le_term l (c1 c2 : ctx) (e1 e2 t1 t2 : exp) fuel : bool :=
  @@[false] fuel =1> fuel';
    (*refl*) ((c1 == c2) && (e1 == e2) && (t1 == t2) && is_easy_wf_term fuel' l c1 e1 t1)
    || (* by *) (is_easy_wf_lang fuel' l && rule_in ({<c1 <# c2 |- e1 <# e2 .: t1 <# t2}) l)
(*TODO: trans, subst (these are the scary cases performance-wise)*)
@@.

Lemma check_passes_and r1 r2 : check! r1 ; r2 <-> r1 && r2.
Proof.
  case: r1; case: r2; simpl; split; eauto.
Qed.

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
  repeat first [ rewrite check_passes_and
          | case /andP
          | view_is_easy_IH_and_intro
          | intro ];
  by eauto.

Theorem is_easy_wf_recognizes fuel
  : (forall l, is_easy_wf_lang fuel l -> wf_lang l)
    /\ (forall l r, wf_lang l -> is_easy_wf_rule fuel l r -> wf_rule l r)
    /\ (forall l c, wf_lang l -> is_easy_wf_ctx fuel l c -> wf_ctx l c)
    /\ (forall l c t, wf_lang l -> is_easy_wf_sort fuel l c t -> wf_sort l c t)
    /\ (forall l c s c', wf_lang l -> is_easy_wf_subst fuel l c s c' -> wf_subst l c s c')
    /\ (forall l c e t, wf_lang l -> is_easy_wf_term fuel l c e t -> wf_term l c e t)
    /\ (forall l c1 c2, wf_lang l -> is_easy_le_ctx l c1 c2 fuel -> le_ctx l c1 c2)
    /\ (forall l c1 c2 t1 t2, wf_lang l -> is_easy_le_sort l c1 c2 t1 t2 fuel -> le_sort l c1 c2 t1 t2).
Proof.
  elim: fuel => //=.
  move => fuel.
  case => [IHlang [IHrule [IHctx [IHsort [IHsubst [IHterm [IHlectx IHlesort]]]]]]].
  split.
  1:{
    case; auto.
    solve_easy_wf_from_hyps.
  }
  split.
  1:{
    move => l.
    case; auto.
    move => c c0 e e0 wfl.
    solve_easy_wf_from_hyps.
    move => c c0 e e0 t t0 wfl.
    solve_easy_wf_from_hyps.
  }
  split.
  1:{
    move => l.
    case; auto.
    move => a l0 wfl.
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
    move => wfl.
    solve_easy_wf_from_hyps.
  }
  split.
  1:{
    move => l c.
    case => //=.
    case => //=; by eauto.
    move => e s.
    case => //=.
    move => a l0 wfl.
    solve_easy_wf_from_hyps.
  }
  split.
  {
    move => l c.
    case => //=.
    move => n t wfl.
    case lne: (List.nth_error c n) =>//=.
    case ta: (t == _a_).
    move: ta => /eqP ->.
    repeat first [ case /andP
                 | view_is_easy_IH_and_intro
                 | intro ].
    constructor; eauto.
    solve_easy_wf_from_hyps.
    unfold lookup_term_args.
    unfold lookup_term_sort.
    move => n s t.
    case lsa: (lookup_rule 0 l n) => //=.
    case: _a_ lsa => //=.
    move => c' t' /lookup_rule_is_nth' => isn wfl.
    case /check_passes_and /andP.
    case teq: (t' [/s /] == t).
    move: teq => /eqP <- => _.
    solve_easy_wf_from_hyps.
    done.
  }
  split.
  1:{
    move => l.
    case => //=.
    case => //=; auto.
    move => t1 c1.
    case => //.
    solve_easy_wf_from_hyps.
  }
  1:{
    intro_to is_true.
    case /orP.
    - case ceq:(c1 == c2) =>//=; move: ceq => /eqP ->.
      case teq:(t1 == t2) =>//=; move: teq => /eqP ->.
      solve_easy_wf_from_hyps.
    - repeat first [ case /andP
          | view_is_easy_IH_and_intro
          | intro ].
      move: b => /rule_inP.
      eauto.
  }
Qed.


Theorem is_easy_le_term_recognizes fuel
  : (forall l c1 c2 e1 e2 t1 t2,
        wf_lang l ->
        is_easy_le_term l c1 c2 e1 e2 t1 t2 fuel ->
        le_term l c1 c2 e1 e2 t1 t2).
Proof.
  elim: fuel => //=.
  intros until t2.
  move => wfl.
  case /orP.
  {
    case ceq: (c1 == c2) => //=; move: ceq => /eqP ->.
    case eeq: (e1 == e2) => //=; move: eeq => /eqP ->.
    case teq: (t1 == t2) => //=; move: teq => /eqP ->.
    move => et.
    eapply is_easy_wf_recognizes in et.
    all: eauto.
  }
  {
    case /andP.
    move => et.
    eapply is_easy_wf_recognizes in et.
    move /rule_inP.
    eauto.
  }
Qed.


Ltac get_is_easy_goal n :=
  match goal with
  | |- wf_lang ?L => type_term (is_easy_wf_lang n L)
  | |- wf_rule ?L ?r => type_term (is_easy_wf_rule n L r)
  | |- wf_ctx ?L ?c => type_term (is_easy_wf_ctx n L c)
  | |- wf_sort ?L ?c ?t => type_term (is_easy_wf_sort n L c t)
  | |- wf_term ?L ?c ?e ?t => type_term (is_easy_wf_term n L c e t)
  | |- wf_subst ?L ?c ?s ?c' => type_term (is_easy_wf_subst n L c s c')
  | |- le_sort ?l ?c1 ?c2 ?t1 ?t2 => type_term (is_easy_le_sort n l c1 c2 t1 t2)
  | |- le_term ?l ?c1 ?c2 ?e1 ?e2 ?t1 ?t2 => type_term (is_easy_le_term n l c1 c2 e1 e2 t1 t2)
  end.

(* Tactics for using the partial recognizer to prove a language well-formed *)
(*TODO: generalize to all constructs, not just langs*)
Ltac solve_easy_wf n :=
  let easy_goal := get_is_easy_goal n in
  suff: easy_goal;
  [ intros; first [ eapply is_easy_wf_recognizes
                  | eapply is_easy_le_term_recognizes]; by eauto
  | by compute].

Tactic Notation "solve_easy_wf" constr(n) := solve_easy_wf n.
Tactic Notation "solve_easy_wf" := solve_easy_wf 1000.
    
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
