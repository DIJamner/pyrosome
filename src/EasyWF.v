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
  : wf_lang l -> wf_ctx l c -> type_wf_term l c e = Some t -> wf_term l c e t.
Proof with eauto with judgment using .
  intro wfl.
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
    intro isn. apply: wf_term_by; eauto.
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
      apply: wf_subst_cons...
    }
    move: isn.
    move /is_nth_level_in /(rule_in_wf wfl).
    inversion...
  }
Qed.    

Lemma type_wf_subst_recognizes l c s c'
  : wf_lang l -> wf_ctx l c -> wf_ctx l c' -> type_wf_subst l c s c' = Some tt -> wf_subst l c s c'.
Proof using .
  intros wfl wfc.
  elim: s c'; intros until c'; case: c'; simpl; try easy; eauto with judgment.
  intros t' c' wfc'.
  inversion wfc'; subst.
  break_option_dos...
  subst.
  intro.
  apply: wf_subst_cons; eauto with judgment.
  apply: type_wf_term_recognizes;
    eauto with judgment.
  match goal with
    H : check (?E) = Some tt |- _ =>
    move:H; case cv: E; simpl; try easy; move => _
  end.
  move: cv => /eqP <-.
  done.
Qed.

Lemma type_wf_sort_recognizes l c t
  : wf_lang l -> wf_ctx l c -> type_wf_sort l c t = Some tt -> wf_sort l c t.
Proof.
  move => wfl.
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
  Unshelve.
  all: auto.
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


Ltac recognize_lang :=
  match goal with
    |- wf_lang ?L =>
    suff: type_wf_lang L = Some tt;
    [ by apply type_wf_lang_recognizes
    | by cbv]
  end.

Ltac recognize_ctx :=  match goal with
    |- wf_ctx ?L ?C =>
    suff: type_wf_ctx L C = Some tt;
    [ apply type_wf_ctx_recognizes
    | by cbv]
  end.

Ltac recognize_sort :=  match goal with
    |- wf_sort ?L ?C ?T =>
    suff: type_wf_sort L C T = Some tt;
    [ apply type_wf_sort_recognizes
    | by cbv]
  end.

Ltac recognize_term :=  match goal with
    |- wf_term ?L ?C ?E ?T =>
    suff: type_wf_term L C E = Some T;
    [ apply type_wf_term_recognizes
    | by cbv]
  end.

Ltac recognize_subst :=  match goal with
    |- wf_subst ?L ?C ?S ?C' =>
    suff: type_wf_subst L C S C' = Some tt;
    [ apply type_wf_subst_recognizes
    | by cbv]
  end.

Ltac recognize_rule' :=
  match goal with
    |- wf_rule ?L ?R =>
    suff: type_wf_rule L R = Some tt;
    [ by apply type_wf_rule_recognizes
    | idtac]
  end.


(*TODO: move to utils *)
Ltac unfold_tail l :=
  match l with
  | _::?l' => unfold_tail l'
  | _ => unfold l
  end.

Ltac wf_lang_eauto :=
   repeat match goal with
          | |- wf_lang ?l => unfold_tail l
         end;
  repeat match goal with
         | |- wf_lang (?R :: ?L) =>
           suff: wf_lang L;
             [intro;
              apply: wf_lang_cons;
              eauto with judgment|]
         | |- wf_lang nil => apply: wf_lang_nil
         end.

(*Todo: For testing only*)
Require Import Setoid Equivalence.

Definition testlang :=
  [:: sort_le [::] (con 1 [::]) (con 0 [::]);
      sort_rule [::];
      sort_rule [::]
  ].

(*
Hint Extern 1 (is_true (is_nth_level _ _ _)) => by compute : judgment.
Lemma wf_test : wf_lang testlang.
Proof.
  unfold testlang.
  wf_lang_eauto.
  constructor; eauto with judgment.
  apply: wf_sort_by;
    auto with judgment.
  (*TODO: need this because the first auto solves an existential variable*)
  auto with judgment.
  
  apply: wf_sort_by; auto with judgment.
  auto with judgment.
Qed.

Goal le_sort testlang [::] (con 1 [::]) (con 1 [::]).
Proof.
  unfold testlang.
  reflexivity.
Qed.  
(*
Goal le_sort testlang [::] (con 1 [::]) (con 0 [::]).
  unfold testlang.
  
  Check le_sort_by.

  rewrite (@le_sort_by testlang [::] [1|] [0|]).
  setoid_replace [1|] with [0|] using relation (le_sort testlang [::]).
  
goal: get rewriting working
 *)

Ltac requiresamevar n1 n2 :=let c1 := constr:(fun n1 n2 : Set⇒ltac:(exact n1)) inlet c2 := constr:(fun n1 n2 : Set⇒ltac:(exact n2)) infirst [ constreq c1 c2|fail 1 "Not the same var:" n1 "and" n2 "(via constreq" c1 c2 ")" ].Ltac issamevar n1 n2 :=match goal with|⇒let:= match goal with⇒requiresamevar n1 n2 end intrue|⇒falseend.

Ltac isunderscore v :=
  let v' := fresh v in
  let v' := fresh v' in
  issamevar v v'.


goal: ltac2 integrated inference algo
*)
