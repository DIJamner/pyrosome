(*********************************************
A partial recognizer for well-formed languages
**********************************************)


Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From excomp Require Import Utils Exp Rule Core.


Import OptionMonad.

Definition nth_level_err {A} l n : option A :=
  if n < size l then List.nth_error l (size l - n.+1) else None.

Lemma is_nth_level_to_fn_err {A:eqType} (l : seq A) n x
  : is_nth_level l n x = (nth_level_err l n == Some x).
Proof using .
  unfold nth_level_err; unfold is_nth_level.
  case: (n < size l); simpl; try easy.
Qed.

(* TODO: differentiate out of fuel? or just calculate enough? or use Function w/ measure? *)

Fixpoint type_wf_term l c e {struct e} : option exp :=
  (* output context not easily inferred; has to be an argument 
       inlined to get termination checking working *)
  let type_wf_subst := fix twfs l c s (c' : ctx) {struct s} : option unit :=
                         match s, c' with
                         | [::], [::] => Some tt
                         | e::s', t::c'' =>
                           do t' <- type_wf_term l c e;
                           do tt <- check (t' == t[/s'/]);
                           twfs l c s' c''
                         | _,_ => None
                         end in
  match e with
  | con n s =>
    do term_rule c' t <- nth_level_err l n;
    do tt <- type_wf_subst l c s c';
    Some t[/s/]
  (* TODO: incorporate into other constrs
         | conv pf e' =>
           do t <- type_wf_term l c e';
           do (t1,t2) <- type_le_sort l c pf;
           do tt <- check (t == t1);
           ret t2 *)
  | var n =>
    do e <- nth_level_err c n;
    Some e
  end.

Definition type_wf_subst := fix twfs l c s (c' : ctx) {struct s} : option unit :=
                              match s, c' with
                              | [::], [::] => Some tt
                              | e::s', t::c'' =>
                                do t' <- type_wf_term l c e;
                                do tt <- check (t' == t[/s'/]);
                                twfs l c s' c''
                              | _,_ => None
                              end. 

Definition type_wf_sort l c (t : exp) : option unit :=
  match t with
  | con n s =>
    do sort_rule c' <- nth_level_err l n;
    do tt <- type_wf_subst l c s c';
    Some tt
  | var _ => None
  end.

Lemma option_id_match {A} (me : option A)
  :  match me with
     | Some e => Some e
     | None => None
     end = me.
Proof using .
  by case me.
Qed.

Ltac break_option_dos :=
  (* TODO: hack for case:*)
  let nxtnxtnxt := fresh "nxtnxtnxt" in
  repeat
    (match goal with
       |-context[match ?e with _ => _ end] =>
       case nxtnxtnxt: e end; try easy;
     let H := fresh "casevar" in move: nxtnxtnxt => H).

Lemma type_wf_term_recognizes l c e t
  : wf_ctx l c -> type_wf_term l c e = Some t -> wf_term l c e t.
Proof with eauto with judgment using .
  elim: e c t.
  {
    simpl; intros until t; intro wfc.
    rewrite option_id_match; move /eqP; rewrite -is_nth_level_to_fn_err...
  }
  {
    intros until t; intro wfc.
    simpl.
    break_option_dos.
    subst.
    case => <-. move: casevar => /eqP.
    rewrite -is_nth_level_to_fn_err.
    intro isn. apply: wf_term_by'; eauto.
    move: isn casevar1.
    match goal with
      |- _ -> _ -> wf_subst _ _ _ ?c => move: c => c' end.
    move => isn.
    suff: wf_ctx l c'.
    clear isn.
    elim: l0 H c'; simpl.
    move => _ c';break_option_dos...
    {
      intro_to and; case => IH1 IH2.
      case; simpl; try easy.
      intros t' c'.
      break_option_dos...
      subst.
      move: (IH1 c _ wfc casevar) => wft.
      move: casevar0.
      unfold check.
      match goal with |-context[if ?A then _ else _] => case aeq: A end; try easy.
      move => _.
      move: aeq wft => /eqP -> wft.
      intros.
      inversion x;  subst.
      apply: wf_subst_cons'...
    }
    move: isn.
    suff: wf_lang l...
    move => wfl.
    move /is_nth_level_in /(rule_in_wf wfl).
    inversion...
  }
Qed.    

Lemma type_wf_subst_recognizes l c s c'
  : wf_ctx l c -> wf_ctx l c' -> type_wf_subst l c s c' = Some tt -> wf_subst l c s c'.
Proof using .
  intros wfc.
  elim: s c'; intros until c'; case: c'; simpl; try easy; eauto with judgment.
  intros t' c' wfc'.
  inversion wfc'; subst.
  break_option_dos...
  subst.
  move /(H c' H4) => wfs.
  apply: wf_subst_cons'; eauto with judgment.
  move: casevar0.
  unfold check.
  match goal with |-context[if ?A then _ else _] => case aeq: A end; try easy.
  move: aeq casevar => /eqP ->.
  move / type_wf_term_recognizes.
  eauto with judgment.
Qed.

Lemma type_wf_sort_recognizes l c t
  : wf_ctx l c -> type_wf_sort l c t = Some tt -> wf_sort l c t.
Proof.
  case: t; simpl; try easy.
  intros n s.
  break_option_dos.
  subst.
  move: casevar => /eqP.
  rewrite - is_nth_level_to_fn_err .
  move => isn; pose p:= isn; move: p.
  move /is_nth_level_in /rule_in_wf.
  intros limplr wfc _.
  suff: wf_lang l; eauto with judgment.
  move /limplr; inversion; try easy.
  subst.
  move: casevar1 => /type_wf_subst_recognizes.
  eauto with judgment.
Qed.

Fixpoint type_wf_ctx l c : option unit :=
  match c with
  | [::] => Some tt
  | t::c' =>
    do tt <- type_wf_sort l c' t;
    type_wf_ctx l c'
  end.


Lemma type_wf_ctx_recognizes l c
  : wf_lang l -> type_wf_ctx l c = Some tt -> wf_ctx l c.
Proof using .
  elim: c; simpl; eauto with judgment.
  intros t c.
  break_option_dos.
  subst.
  move => H /H => H1 /H1.
  move: casevar => /type_wf_sort_recognizes.
  eauto with judgment.
Qed.

Definition type_wf_rule l r : option unit :=
  match r with
  | sort_rule c => type_wf_ctx l c
  | term_rule c t =>
    do tt <- type_wf_sort l c t;
    type_wf_ctx l c
  | sort_le c t1 t2 =>
    do tt <- type_wf_sort l c t1;
    do tt <- type_wf_sort l c t2;
    type_wf_ctx l c
  | term_le c e1 e2 t =>
    do t1 <- type_wf_term l c e1;
    do t2 <- type_wf_term l c e2;
    do tt <- check (t == t1);
    do tt <- check (t == t2);
    type_wf_ctx l c
  end.

Lemma type_wf_rule_recognizes l r
  : wf_lang l -> type_wf_rule l r = Some tt -> wf_rule l r.
Proof using .
  case: r; simpl; intro_to wf_lang; break_option_dos; intro wfl; subst.
  all: move /type_wf_ctx_recognizes.
  eauto with judgment.
  all: repeat match goal with
  | H : type_wf_sort _ _ _= Some tt |- _ =>
    move: H => /type_wf_sort_recognizes
  end; eauto 7 with judgment.

  move: casevar1 casevar3.
  repeat match goal with
           |- context[check ?B] =>
           case nxt: B; move: nxt; simpl; move /eqP
         end; try easy.
  move ->.
  intro; subst.
  repeat match goal with
         | H : type_wf_term _ _ _ = Some _ |- _ =>
           move: H => /type_wf_term_recognizes
         end; eauto 7 with judgment.
Qed.  

Fixpoint type_wf_lang l : option unit :=
  match l with
  | [::] => Some tt
  | r::l' =>
    do tt <- type_wf_rule l' r;
    type_wf_lang l'
  end.

Lemma type_wf_lang_recognizes l
  : type_wf_lang l = Some tt -> wf_lang l.
Proof using .
  elim: l; simpl; eauto with judgment; intros r l; break_option_dos.
  intros.
  subst.
  move: casevar => /type_wf_rule_recognizes.
  eauto with judgment.
Qed.


  (*

Definition lookup_sort_args l n : option ctx :=
  match nth_level l n with
  | Some ({| c |- sort}) => Some c
  | _ => None
  end.
Hint Unfold lookup_sort_args.
Hint Transparent lookup_sort_args.

Definition lookup_term_args l n : option ctx :=
  match nth_level l n with
  | Some ({| c |- _}) => Some c
  | _ => None
  end.
Hint Unfold lookup_term_args.
Hint Transparent lookup_term_args.

Definition lookup_term_sort l n : option exp :=
  match nth_level l n with
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


(*TODO: move error messaging code into separate file/library *)
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

Definition wf_result_alt r1 : wf_result -> wf_result :=
  match r1 with
  | wf_success => fun _ => wf_success
  (*TODO: figure out the best way to incorporate left branch's error message *)
  | _ => id
  end.

Notation "check! r1 ; r2" := (wf_result_seq r1 r2) (at level 80, right associativity).

Notation "r1 <||> r2" := (wf_result_alt r1 r2) (at level 70).

Notation "check![ es ] b1 ; r" :=
  (wf_result_seq (if b1 then wf_success else wf_error es) r)
    (at level 80, right associativity).

(*TODO: notation or fn call*)
Definition wf_result_ctx c r1 : wf_result :=
  match r1 with
  | wf_success => wf_success
  | wf_no_fuel => wf_no_fuel
  | wf_error s => wf_error (c ++ "; " ++ s)
  end.

Notation "ctx[ c ]" := (wf_result_ctx c).

Lemma wf_result_ctx_id c r : (ctx[c] r : bool) = (r : bool).
Proof.
  case: r; simpl; auto.
Qed.

Lemma check_passes_and r1 r2 : (check! r1 ; r2 : bool) = r1 && r2.
Proof.
  case: r1; case: r2; simpl; split; eauto.
Qed.

Lemma default_as_bool {A} (default : wf_result) (val : option A) (body : A -> wf_result)
  : (match val with
     | Some x => body x
     | None => default
     end : bool)
    = (match val with
       | Some x => (body x) : bool
       | None => default : bool
       end : bool).
Proof.
  case val; eauto.
Qed.

Lemma alt_as_or r1 r2 : (r1 <||> r2 : bool) = r1 || r2.
Proof.
  case: r1; case: r2; simpl; split; eauto.
Qed.

Lemma if_distr_bool b (r2 r3 : wf_result)
  : ((if b then r2 else r3) : bool) = if b then r2 : bool else r3 : bool.
Proof.
  case: b; auto.
Qed.

Ltac result_as_bool :=
  rewrite ?default_as_bool ?wf_result_ctx_id ?check_passes_and ?alt_as_or ?if_distr_bool;
  change (wf_success : bool) with true;
  change (wf_no_fuel : bool) with false;
  change (wf_error _ : bool) with false.


(*TODO: give contexts for errors*)

Fixpoint is_easy_wf_sort fuel :=
  @@[fun l c t => wf_no_fuel] fuel =1> fuel';
    fun l c t =>
    match t with
    | var x => wf_error ("Variables like " ++ printnat x ++ " are not valid sorts")
    | con n s =>
      c' <-[wf_error ("Sort rule " ++ printnat n ++ " out of bounds")] lookup_sort_args l n;
      ctx["In sort " ++ print t] (is_easy_wf_subst fuel' l c s c')
    end@@
with is_easy_wf_subst fuel : lang -> ctx -> subst -> ctx -> wf_result :=
       @@[fun l c s c' => wf_no_fuel] fuel =1> fuel';
         fun l c s c' => match s, c' with
         | [::], [::] => is_easy_wf_ctx fuel' l c
         | e::s', t::c'' =>
           check! is_easy_wf_sort fuel' l c'' t;
           check! is_easy_wf_term fuel' l c e t[/s' /];
             is_easy_wf_subst fuel' l c s' c''
         | _, _ => wf_error "Substitution and output context of different lengths"
         end@@
with is_easy_wf_term fuel : lang -> ctx -> exp -> exp -> wf_result :=
       @@[fun l c e t => wf_no_fuel] fuel =1> fuel';
         fun l c e t => match e with
         | var x =>
           t' <-[wf_error ("Term variable " ++ printnat x ++ " out of bounds")] List.nth_error c x;
           check!["Variable type mismatch; expected " ++ print t ++ " but found " ++ print t'] t == t';
           is_easy_wf_ctx fuel' l c
           (*TODO: get this to work && is_easy_le_sort l c c t' t fuel'*)
         | con n s =>
           let outofbounds_err := ("Term constructor " ++ printnat n ++ " out of bounds")%string in
           c' <-[wf_error outofbounds_err] lookup_term_args l n;
           t' <-[wf_error outofbounds_err] lookup_term_sort l n;
           check!["Constructor type mismatch"] t'[/s/] == t;
           ctx["In term " ++ print e ++ " with sort " ++ print t](is_easy_wf_subst fuel' l c s c')
         end@@
with is_easy_wf_ctx fuel : lang -> ctx -> wf_result :=
       @@[fun l c => wf_no_fuel] fuel =1> fuel';
         fun l c => match c with
         | [::] => wf_success
         | t::c' =>
           check! is_easy_wf_sort fuel' l c' t;
           is_easy_wf_ctx fuel' l c'
         end@@.
Fixpoint is_easy_wf_lang fuel : lang -> wf_result :=
       @@[fun l =>  wf_no_fuel] fuel =1> fuel';
         fun l => match l with
         | [::] => wf_success
         | r::l' => check! is_easy_wf_rule fuel' l' r;
                      is_easy_wf_lang fuel' l'
         end@@
with is_easy_wf_rule fuel :=
       @@[fun l r => wf_no_fuel] fuel =1> fuel';
         fun l r => match r with
         | {| c |- sort } => is_easy_wf_ctx fuel' l c
         | {| c |- t } => is_easy_wf_sort fuel' l c t
         | {< c1 <# c2 |- t1 <# t2 } =>
           check! is_easy_le_ctx l c1 c2 fuel';
           check! is_easy_wf_sort fuel' l c1 t1;
           is_easy_wf_sort fuel' l c2 t2
         | {< c1 <# c2 |- e1 <# e2 .: t1 <# t2 } =>
           check! is_easy_le_sort l c1 c2 t1 t2 fuel';
             check! is_easy_wf_term fuel' l c1 e1 t1;
             is_easy_wf_term fuel' l c2 e2 t2
         end@@
with is_easy_le_sort l (c1 c2 : ctx) (t1 t2 : exp) fuel :=
       @@[wf_no_fuel] fuel =1> fuel';
         (*TODO:include ctxts in error message*)
         (check!["Contexts unequal"] c1 == c2;
         check!["Sorts " ++ print t1 ++ " and " ++ print t2 ++ " unequal"] t1 == t2;
         is_easy_wf_sort fuel' l c1 t1)
           <||> (* by *) (check! is_easy_wf_lang fuel' l;
                            (*TODO:better message*)
                            check!["Rule is in"] ({<c1 <# c2 |- t1 <# t2}) \in l;
                         wf_success)
    (*TODO: trans, subst (these are the scary cases performance-wise)*)
    @@
with is_easy_le_ctx l (c1 c2 : ctx) fuel :=
       @@[wf_no_fuel] fuel =1> fuel';
       match c1, c2 with
       | [::],[::] => is_easy_wf_lang fuel' l
       | t1::c1',t2::c2' => is_easy_le_sort l c1' c2' t1 t2 fuel'
       | _, _ => wf_error "TODO: write error message"
       end@@.


Definition is_easy_le_term l (c1 c2 : ctx) (e1 e2 t1 t2 : exp) fuel : bool :=
  @@[false] fuel =1> fuel';
    (*refl*) ((c1 == c2) && (e1 == e2) && (t1 == t2) && is_easy_wf_term fuel' l c1 e1 t1)
    || (* by *) (is_easy_wf_lang fuel' l && ({<c1 <# c2 |- e1 <# e2 .: t1 <# t2} \in l))
(*TODO: trans, subst (these are the scary cases performance-wise)*)
@@.

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
  result_as_bool;
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
  elim: fuel; try by move => //=.
  move => fuel.
  case => [IHlang [IHrule [IHctx [IHsort [IHsubst [IHterm [IHlectx IHlesort]]]]]]].
  split;[case; auto; solve_easy_wf_from_hyps|].
  split;[move => l; case; auto; intro_to is_true; solve_easy_wf_from_hyps|].
  split;[move => l; case; auto; intro_to is_true; solve_easy_wf_from_hyps|].
  split;[move => l c; case; auto; intro_to is_true|].
  {
    simpl.    
    unfold lookup_sort_args.
    case lsa: (nth_level l n) => //=.
    case: _a_ lsa => //=.
    move => c' /eqP => isn.
    rewrite wf_result_ctx_id.
    move => wfs.
    econstructor.
    rewrite <- nth_level_confluent; eauto.
    solve_easy_wf_from_hyps.
  }
  split;[move => l c; case; [case|]; eauto;
         move => e s; case; auto;
         intro_to is_true;
         solve_easy_wf_from_hyps|].
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
    case lsa: (nth_level l n) => //=.
    case: _a_ lsa => //=.
    move => c' t' /eqP => isn wfl.
    result_as_bool.
    case /andP.
    case teq: (t' [/s /] == t).
    move: teq => /eqP <- => _.
    rewrite wf_result_ctx_id.
    move => wfs.
    econstructor.
    rewrite <- nth_level_confluent; eauto.
    solve_easy_wf_from_hyps.
    solve_easy_wf_from_hyps.
  }
  split;[move => l; case => //=; [case; by auto|];
        move => t1 c1; case => //; solve_easy_wf_from_hyps|].
  {
    intro_to is_true.
    result_as_bool.
    case /orP.
    - case ceq:(c1 == c2) =>//=; move: ceq => /eqP ->.
      case teq:(t1 == t2) =>//=; move: teq => /eqP ->.
      solve_easy_wf_from_hyps.
    - repeat first [ case /andP
          | view_is_easy_IH_and_intro
          | intro ].
      move: b.
      result_as_bool.
      case /andP => /IHlang => wfl.
      case /andP.
      result_as_bool.
      case req: (({<c1 <# c2 |- t1 <# t2}) \in l); eauto.
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
   let easy_goal := get_is_easy_goal 100 in
  suff: easy_goal;
  [ intros; first [ eapply is_easy_wf_recognizes
                  | eapply is_easy_le_term_recognizes]; by eauto|
    let p := fresh in
    pose p:= easy_goal;
    change easy_goal with p;
    cbv in p;
    match eval cbv in p with
    | wf_success => by cbv
    | wf_no_fuel => fail 0 "is_easy_wf out of fuel"
    | wf_error ?msg => fail 0 msg
    end ].

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
*)
