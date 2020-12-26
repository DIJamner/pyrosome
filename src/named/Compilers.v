
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From Utils Require Import Utils.
From Named Require Import Exp Rule Core.

Require Import String.

(* TODO: this does not admit for optimization *)
Variant compiler_case : Set :=
| sort_case : list string (* holes *) -> (* target *) sort -> compiler_case
| term_case :  list string (* holes *) -> (* target *) exp -> compiler_case.

Definition eq_compiler_case c1 c2 : bool :=
  match c1,c2 with
  | sort_case args1 t1, sort_case args2 t2 =>
    (args1 == args2) && (t1 == t2)
  | term_case args1 e1, term_case args2 e2 =>
    (args1 == args2) && (e1 == e2)
  | _,_ => false
  end.

Lemma eq_compiler_caseP c1 c2 : reflect (c1 = c2) (eq_compiler_case c1 c2).
Proof using .
  destruct c1; destruct c2; simpl;  solve_reflect_norec.
Qed.

Definition compiler_case_eqMixin := Equality.Mixin eq_compiler_caseP.

Canonical compiler_case_eqType := @Equality.Pack compiler_case compiler_case_eqMixin.

(* each element is the map for that constructor *)
Definition compiler := named_list compiler_case. 


Fixpoint compile_term (cmp : compiler) (e : exp) : exp :=
  match e with
  | var x => var x
  | con n s =>
    let default := sort_case [::] (scon "ERR" [::]) in
    let arg_terms := map (compile_term cmp) s in
    match named_list_lookup default cmp n with
    | term_case args c_case => c_case[/zip args arg_terms /]
    | _ => con "ERR"%string [::]
    end
  end.

Definition compile_args cmp := map (compile_term cmp).

Definition compile_sort (cmp : compiler) (e : sort) : sort :=
  match e with
  | scon n s =>
    let default := term_case [::] (con "ERR" [::]) in
    let arg_terms := compile_args cmp s in
    match named_list_lookup default cmp n with
    | sort_case args c_case => c_case[/zip args arg_terms/]
    | _ => scon"ERR"%string [::]
    end
  end.

Definition compile_subst (cmp : compiler) (e : subst) : subst :=
  map (fun p => (fst p, compile_term cmp (snd p))) e.

Definition compile_ctx (cmp : compiler) (e : ctx) : ctx :=
  map (fun p => (fst p, compile_sort cmp (snd p))) e.

(*

First we specify the properties in terms of compile,
then inductively on the compiler. TODO: prove equivalent
 *)
Definition sort_wf_preserving_sem cmp l1 l2 :=
  forall c t, wf_sort l1 c t ->
              wf_sort l2 (compile_ctx cmp c) (compile_sort cmp t).

Definition term_wf_preserving_sem cmp l1 l2 :=
  forall c e t, wf_term l1 c e t ->
                wf_term l2 (compile_ctx cmp c) (compile_term cmp e) (compile_sort cmp t).

Definition sort_le_preserving_sem cmp l1 l2 :=
  forall c t1 t2, le_sort l1 c t1 t2 ->
                  le_sort l2 (compile_ctx cmp c) (compile_sort cmp t1) (compile_sort cmp t2).

Definition term_le_preserving_sem cmp l1 l2 :=
  forall c e1 e2 t, le_term l1 c t e1 e2 ->
                    le_term l2 (compile_ctx cmp c) (compile_sort cmp t)
                        (compile_term cmp e1) (compile_term cmp e2).

Definition args_wf_preserving_sem cmp l1 l2 :=
  forall c s' c', wf_args l1 c s' c' ->
                    wf_args l2 (compile_ctx cmp c) (map (compile_term cmp) s')
                            (compile_ctx cmp c').

Definition ctx_wf_preserving_sem cmp l1 l2 :=
  forall c , wf_ctx l1 c ->
             wf_ctx l2 (compile_ctx cmp c).

Definition args_le_preserving_sem cmp l1 l2 :=
  forall c s1 s2 c', le_args l1 c c' s1 s2 ->
                     le_args l2 (compile_ctx cmp c) (compile_ctx cmp c')
                        (map (compile_term cmp) s1) (map (compile_term cmp) s2).
  

Definition semantics_preserving cmp l1 l2 :=
  sort_wf_preserving_sem cmp l1 l2
  /\ term_wf_preserving_sem cmp l1 l2
  /\ args_wf_preserving_sem cmp l1 l2
  /\ sort_le_preserving_sem cmp l1 l2
  /\ term_le_preserving_sem cmp l1 l2
  /\ args_le_preserving_sem cmp l1 l2.

(*TODO: this is an equal stronger property (which?); includes le principles;
  formalize the relationship to those above and le semantic statements *)
Inductive preserving_compiler (target : lang) : compiler -> lang -> Prop :=
| preserving_compiler_nil : preserving_compiler target [::] [::]
| preserving_compiler_sort : forall cmp l n c t,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    wf_sort target (compile_ctx cmp c) t ->
    preserving_compiler target ((n, sort_case (map fst c) t)::cmp) ((n,sort_rule c) :: l)
| preserving_compiler_term : forall cmp l n c e t,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c, t *)
    wf_term target (compile_ctx cmp c) e (compile_sort cmp t) ->
    preserving_compiler target ((n,term_case (map fst c) e)::cmp) ((n,term_rule c t) :: l)
| preserving_compiler_sort_le : forall cmp l n c t1 t2,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    le_sort target (compile_ctx cmp c)
            (compile_sort cmp t1)
            (compile_sort cmp t2) ->
    preserving_compiler target cmp ((n,sort_le c t1 t2) :: l)
| preserving_compiler_term_le : forall cmp l n c e1 e2 t,
    preserving_compiler target cmp l ->
    (* Notable: only uses the previous parts of the compiler on c *)
    le_term target (compile_ctx cmp c)
            (compile_sort cmp t)
            (compile_term cmp e1)
            (compile_term cmp e2) ->
    preserving_compiler target cmp ((n,term_le c e1 e2 t) :: l).

Lemma wf_empty_sort c t : ~wf_sort [::] c t.
Proof using .
  by inversion.
Qed.

Lemma wf_empty_ctx c : wf_ctx [::] c -> c = [::].
Proof using .
  case; auto.
  intros.
  exfalso.
  eapply wf_empty_sort; eassumption.
Qed.


Lemma wf_empty_term c e t : wf_ctx [::] c -> ~wf_term [::] c e t.
Proof using .
  intros wfc wft.
  elim: wft wfc; eauto.
  intros n t0 nin.
  move /wf_empty_ctx => wfe.
  move: wfe nin => ->.
  auto.  
Qed.


Lemma le_empty_term c e1 e2 t : le_term [::] c t e1 e2 -> e1 = e2
with le_empty_subst c s1 s2 c' : le_subst [::] c c' s1 s2 -> s1 = s2.
Proof using .
  all: case; intros.
  {
    f_equal; eauto.
  }
  { easy. }
  { reflexivity. }
  { apply le_empty_term in l.
    apply le_empty_term in l0.
    rewrite l l0; reflexivity.
  }
  {
    symmetry.
    eapply le_empty_term; eassumption.
  }
  {
    eapply le_empty_term; eassumption.
  }
  { reflexivity. }
  {
    f_equal.
    f_equal.
    eauto.
    eauto.
  }
Qed.
  
Lemma le_empty_sort c t1 t2 : le_sort [::] c t1 t2 -> t1 = t2.
Proof using .
  elim; intros; try by (cbv in *; eauto).
  f_equal; eauto using le_empty_subst.
  by rewrite H0 -H2.
Qed.    

(*TODO: move to core*)

Lemma with_names_from_nil_r (c : ctx) : with_names_from c (@nil exp) = [::].
Proof.
  case: c; simpl; auto; case; auto.
Qed.



Ltac f_equal_match :=
  match goal with
  | [|- match ?e with _ => _ end = match ?e with _ => _ end]
    => let e':= fresh in remember e as e'; destruct e'
  end.

(*
Lemma lookup_in_tail c c' n t s s'
    : let cs' := with_names_from (c'++ c) (s' ++ s) in
    size s == size c ->
    size s' == size c' ->
    all_fresh (c' ++ c) ->
    (n,t) \in c ->
              named_list_lookup (var n) cs' n =
              named_list_lookup (var n) (with_names_from c s) n.
Proof.
  simpl.
  elim: c' s'.
  {
    case; simpl; auto.
    intros a l _.
    move /eqP; inversion.
  }
  {
    intros until s'.
    case: s'.
    {
      intro b.
      move /eqP; inversion.
    }
    {
      destruct a.
      intros e s' szeq.
      simpl; move /eqP; case; move /eqP => szeq'.
      move /andP => [fs0 nlaf] nin.
      suff: ((n=?s0)%string = false); [move ->; eauto|].
      admit.
    }
  }
Admitted.
*)

Lemma fresh_compile_ctx c cmp n
  : fresh n c -> fresh n (compile_ctx cmp c).
Proof using.
  elim: c; simpl; auto.
  move => [n' t] c'.
  unfold fresh.
  intro IH; simpl.
  rewrite !in_cons.
  move /norP => [nneq nnin].
  apply /norP.
  split; auto.
Qed.

Local Ltac in_preserving_sort_rec :=
  intros;
      match goal with
        [ Hin : is_true(_\in_),
          IH : is_true(_\in_) -> exists t,_ |- _] =>
        move: (IH Hin); case; intros
      end; solve [eauto 3 | eexists; rewrite in_cons; apply /orP; eauto].

Lemma in_preserving_sort lt cmp ls n c'
  : preserving_compiler lt cmp ls ->
    (n, sort_rule c') \in ls ->
    exists t,(n, sort_case (map fst c') t) \in cmp.
Proof using .
  elim; simpl; eauto; intros;
    try  match goal with
    [ H : is_true(_\in_::_)|- _] =>
    revert H; rewrite in_cons; move /orP; case
    end; try solve [move/eqP; case; done| in_preserving_sort_rec].
  { 
    move /eqP => [neq ceq].
    subst.
    exists t.
    rewrite in_cons.
    apply /orP.
    left.
    apply /eqP; reflexivity.
  }
  Unshelve.
  exact (scon "ERR" [::]).
Qed.

Lemma in_preserving_term lt cmp ls n c' t
  : preserving_compiler lt cmp ls ->
    (n, term_rule c' t) \in ls ->
    exists e,(n, term_case (map fst c') e) \in cmp.
Proof using .
  elim; simpl; eauto; intros;
    try  match goal with
    [ H : is_true(_\in_::_)|- _] =>
    revert H; rewrite in_cons; move /orP; case
    end; try solve [move/eqP; case; done| in_preserving_sort_rec].
  { 
    move /eqP => [neq ceq teq].
    subst.
    exists e.
    rewrite in_cons.
    apply /orP.
    left.
    apply /eqP; reflexivity.
  }
  Unshelve.
  exact (con "ERR" [::]).
Qed.

Lemma named_list_all_fresh_lookup {A : eqType} l n (e default : A)
  : all_fresh l ->
    (n, e) \in l ->
    named_list_lookup default l n = e.
Proof using .
  elim: l; [ by cbv |].
  move => [n' e'] l IH; simpl.
  move /andP => [ fn allf].
  rewrite in_cons.
  case neq: (n == n').
  case eeq: (e == e').
  {
    move: neq eeq => /eqP neq /eqP eeq.
    rewrite -!neq -!eeq.
    move /orP; case; intros; subst;
    rewrite eqb_refl; reflexivity.
  }
  {
    pose neq' := neq.
    cbn.
    cbn in neq.
    rewrite neq.
    rewrite eeq.
    simpl.
    clear IH.
    move: neq' fn => /eqP ->.
    intros.
    exfalso.
    pose p := (fresh_neq_in fn H).
    move: p.
    move /eqP.
    done.
  }
  {
    suff: ((n, e) == (n', e') = false); [ move ->; simpl|].
    2:{
      rewrite -Bool.negb_true_iff.
      apply /negP.
      move /eqP.
      case.
      move /eqP.
      by rewrite neq.
    }
    pose p := neq; cbn in p; rewrite p; clear p.
    auto.
  } 
Qed.

Lemma preserving_compiler_fresh n lt cmp ls
  : preserving_compiler lt cmp ls ->
    fresh n ls ->
    fresh n cmp.
Proof using .
  elim; simpl; auto; solve
  [unfold fresh; intro_to is_true;
  simpl;
  rewrite !in_cons !negb_or; simpl;
  move /andP; case; intros; try apply /andP; auto].
Qed.

  
Lemma preserving_compiler_all_fresh lt cmp ls
  : preserving_compiler lt cmp ls ->
    all_fresh ls ->
    all_fresh cmp.
Proof using .
  elim; simpl; auto; intro_to is_true;
    move /andP => [frn af]; auto; apply /andP; split; auto.
  all: eapply preserving_compiler_fresh;eauto.
Qed. 
Hint Resolve preserving_compiler_all_fresh : judgment.

(* TODO: move to Core *)
Lemma wf_lang_all_fresh l : wf_lang l -> all_fresh l.
Proof.
  elim; intros; simpl in *; auto.
  apply /andP; auto.
Qed.
Hint Resolve wf_lang_all_fresh : judgment.


Lemma term_fresh_strengthen n cc l cmp c e t
  : fresh n l ->
    wf_term l c e t ->
    compile_term ((n, cc) :: cmp) e = compile_term cmp e
with args_fresh_strengthen n cc l cmp c s c'
  : fresh n l ->
    wf_args l c s c' ->
    compile_args ((n, cc) :: cmp) s = compile_args cmp s.
Proof using .
  {
    intro_to wf_term; inversion; subst; simpl in *; eauto.
    {
      suff: ((n0 =? n)%string = false);[ move ->|].
      {
        f_equal_match; auto.
        change (map (compile_term ?cmp)) with (compile_args cmp).
        erewrite args_fresh_strengthen; eauto.
      }
      {
        apply /negP.
        apply /negP.
        eapply fresh_neq_in; eauto.
      }
    }
  }
  {
    intro_to wf_args; inversion; subst; simpl in *; eauto.
    f_equal; eauto.
  }    
Qed.    
    
Lemma sort_fresh_strengthen n cc l cmp c t
  : fresh n l ->
    wf_sort l c t ->
    compile_sort ((n, cc) :: cmp) t = compile_sort cmp t.
Proof using .
  intro_to wf_sort; inversion; subst.
  simpl.
  suff: ((n0 =? n)%string = false);[ move ->|].
  {
    f_equal_match; auto.
    erewrite args_fresh_strengthen; eauto.
  }
  {
    apply /negP.
    apply /negP.
    eapply fresh_neq_in; eauto.
  }
Qed.
  
Lemma ctx_fresh_strengthen n cc l cmp c
  : fresh n l ->
    wf_ctx l c ->
    compile_ctx ((n, cc) :: cmp) c = compile_ctx cmp c.
Proof.
  elim: c; simpl; auto.
  intro_to wf_ctx; inversion; subst.
  simpl.
  f_equal; auto.
  erewrite sort_fresh_strengthen; eauto.
Qed.  


(*TODO:move to Core*)
(* TODO:add hints?
(* a hint for a common case*)
Lemma wf_ctx_from_sort_rule_in l c n
  : wf_lang l -> (n, sort_rule c) \in l -> wf_ctx l c.
Proof.
  intros wfl cin; apply rule_in_wf in cin; inversion cin; done.
Qed.
Hint Resolve wf_ctx_from_sort_rule_in : judgment.
(* a hint for a common case*)
Lemma wf_ctx_from_term_rule_in l c t n
  : wf_lang l -> (n, term_rule c t) \in l -> wf_ctx l c.
Proof.
  intros wfl cin; apply rule_in_wf in cin; inversion cin; done.
Qed.
Hint Resolve wf_ctx_from_term_rule_in : judgment.
(* a hint for a common case*)
Lemma wf_sort_from_term_rule_in l c t n
  : wf_lang l -> (n, term_rule c t) \in l -> wf_sort l c t.
Proof.
  intros wfl cin; apply rule_in_wf in cin; inversion cin; done.
Qed.
Hint Resolve wf_sort_from_term_rule_in : judgment.
*)

(* TODO: move to utils*)
(* decomposes the way you want \in to on all_fresh lists*)
Fixpoint in_once {A:eqType} n e (l : named_list A) : bool :=
  match l with
  | [::] => false
  | (n',e')::l' =>
    ((n == n') && (e == e')) || ((n != n')&&(in_once n e l'))
  end.

Arguments in_once {A} n e !l/.

Lemma in_once_notin {A:eqType} n (e : A) l
  : n \notin (map fst l) -> ~~(in_once n e l).
Proof using .
  elim: l; auto; intros; break; simpl in *.
  rewrite ?in_cons in H0.
  move: H0.
  case neq: (n==s); auto.
Qed.

Lemma all_fresh_in_once {A:eqType} n (e : A) l
  : all_fresh l -> ((n,e) \in l) = in_once n e l.
Proof using .
  elim: l; simpl; auto; intros; repeat (break; simpl in * ).
  rewrite in_cons.
  rewrite H; auto.
  change ((n,e)==(s,s0)) with ((n==s)&&(e==s0)).
  case neq: (n == s); simpl; auto.
  rewrite Bool.orb_false_r.
  case eeq:(e==s0); simpl; auto.
  apply /negP.
  apply /negP.
  move: neq => /eqP ->.
  by apply in_once_notin.
Qed.  


Local Ltac setup_inv_lem :=
  let pc := fresh "pc" in
  let wfl := fresh "wfl" in
  let frls := fresh "frls" in
  let frcmp := fresh "frcmp" in
  intros pc wfl;
  suff: all_fresh ls; eauto with judgment;  intro frls;
  suff: all_fresh cmp; eauto with judgment; intro frcmp;
  rewrite !all_fresh_in_once; auto;
  revert pc wfl frls frcmp.

Local Ltac inv_lem_step :=
  match goal with
  | H : wf_lang (_::_)|-_=> inversion H; subst; clear H
  | H : wf_rule _ _|-_=>inversion H; subst; clear H
  | H : is_true(_ || _) |- _=> move: H => /orP; case => H; break
  | H : is_true(_ == _) |- _=> move: H => /eqP; (try by inversion); repeat case; intros; subst
  | H : is_true(?a != ?a) |- _=> by rewrite eq_refl in H
  | H : is_true(in_once _ _ _) |- wf_ctx _ _ =>
    rewrite -all_fresh_in_once in H; auto; apply rule_in_wf in H; inversion H; subst; eassumption
  | H : is_true(in_once _ _ _) |- wf_sort _ _ _ =>
    rewrite -all_fresh_in_once in H; auto; apply rule_in_wf in H; inversion H; subst; eassumption
  | H : is_true(in_once _ _ _) |- wf_term _ _ _ _ =>
    rewrite -all_fresh_in_once in H; auto; apply rule_in_wf in H; inversion H; subst; eassumption
  | |- context[ compile_ctx (_::_) _] => erewrite ctx_fresh_strengthen; eauto with judgment
  | |- context[ compile_sort (_::_) _] => erewrite sort_fresh_strengthen; eauto with judgment
  | |- context[ compile_term (_::_) _] => erewrite term_fresh_strengthen; eauto with judgment
  end.

Local Ltac prove_inv_lem :=
  setup_inv_lem;
  elim; [by cbv|..];
    intros; simpl in *; break;
  repeat inv_lem_step; eauto.

Lemma preserving_sort_case_inv n t c lt cmp ls
  :  preserving_compiler lt cmp ls ->
     wf_lang ls ->
     (n, sort_rule c) \in ls ->
     (n, sort_case (map fst c) t) \in cmp ->
     wf_sort lt (compile_ctx cmp c) t.
Proof using . prove_inv_lem. Qed.

Lemma preserving_term_case_inv n t e c lt cmp ls
  :  preserving_compiler lt cmp ls ->
     wf_lang ls ->
     (n, term_rule c t) \in ls ->
     (n, term_case (map fst c) e) \in cmp ->
     wf_term lt (compile_ctx cmp c) e (compile_sort cmp t).
Proof using . prove_inv_lem. Qed.


Lemma preserving_sort_le_inv n t1 t2 c lt cmp ls
  :  preserving_compiler lt cmp ls ->
     wf_lang ls ->
     (n, sort_le c t1 t2) \in ls ->
     le_sort lt (compile_ctx cmp c) (compile_sort cmp t1) (compile_sort cmp t2).
Proof using . prove_inv_lem. Qed.

Lemma preserving_term_le_inv n t e1 e2 c lt cmp ls
  :  preserving_compiler lt cmp ls ->
     wf_lang ls ->
     (n, term_le c e1 e2 t) \in ls ->
     le_term lt (compile_ctx cmp c) (compile_sort cmp t) (compile_term cmp e1) (compile_term cmp e2).
Proof using . prove_inv_lem. Qed.


Lemma f_apply_case_map {A B} (f : A -> B) cc b1 b2
  : f match cc with
      | sort_case args c_case => b1 args c_case
      | term_case args c_case => b2 args c_case
      end
    = match cc with
      | sort_case args c_case => f (b1 args c_case)
      | term_case args c_case => f (b2 args c_case)
      end.
Proof.
  case: cc; reflexivity.
Qed.


Lemma subst_zip args s s'
  : (zip args s)[/s'/] = zip args s[/s'/].
Proof.
  elim: args s; intros until s; case: s; intros; break; simpl in *; auto.
  f_equal.
  by fold_Substable.
Qed.


(* TODO: finish these
Lemma compile_subst_lookup s n cmp
  : compile_term cmp (subst_lookup s n) = subst_lookup (compile_subst cmp s) n.
Proof.
  elim: s; intros; break; simpl in *; auto.
  change (?n =? ?s)%string with (n==s).
  case neq: (n == s); simpl in *; auto.
Qed.

Lemma compile_term_subst cmp e s
  : well_scoped (map fst s) e -> compile_term cmp (e[/s/]) = (compile_term cmp e)[/compile_subst cmp s/]
with compile_args_subst cmp e s
  : well_scoped (map fst s) e -> compile_args cmp (e[/s/]) = (compile_args cmp e)[/compile_subst cmp s/].
Proof.
  {
    case: e; intros; simpl in *; auto using compile_subst_lookup.
    case_match; simpl; auto.
    rewrite subst_assoc; fold_Substable.
    {
      rewrite subst_zip.
      unfold compile_args in *.
      by rewrite compile_args_subst.
    }
    {
      Search _ (map _ (zip _ _)).
(* TODO: ws assumption; need ws_compiler
 *)
Admitted.
Proof.
  (* TODO: requires induction *)
Admitted.

Lemma compile_sort_subst cmp t s
  : compile_sort cmp (t[/s/]) = (compile_sort cmp t)[/compile_subst cmp s/].
Proof.
  case: t; simpl.
  intros n a.
  case_match; simpl; auto.
  rewrite subst_assoc.
  fold_Substable.
  rewrite subst_zip.
  Lemma subst_zip
    : (zip args s)[/s'/] = zip args s[/s'/].
  rewrite (f_apply_case_map (sort_subst (compile_subst cmp s))).
  f_equal_match; simpl; auto.
Admitted.




Lemma with_names_from_zip c s
  : with_names_from c s = zip (map fst c) s.
Proof.
  elim: c s; [| case]; intros until s; case: s; simpl; auto.
  intros.
  f_equal.
  eauto.
Qed.


Lemma compile_with_names_from cmp c s
  : compile_subst cmp (with_names_from c s)
    = with_names_from c (map (compile_term cmp) s).
Proof.
  elim: c s; [| case]; intros until s; case: s; simpl; auto.
  intros.
  f_equal.
  eauto.
Qed.


Lemma compile_ctx_in cmp n t c
  : (n,t) \in c -> (n, compile_sort cmp t) \in compile_ctx cmp c.
Proof.
  elim: c; simpl; auto.
  case; intro_to is_true.
  rewrite in_cons.
  move /orP; case.
  {
    move /eqP; case; intros; subst.
    rewrite in_cons.
    apply /orP; left.
    apply /eqP; f_equal.
  }
  {
    simpl.
    intro.
    rewrite in_cons.
    apply /orP; auto.
  }
Qed.


Lemma compile_ctx_fst c cmp : map fst (compile_ctx cmp c) = map fst c.
Proof.
  elim: c; auto.
  case => n s l //= -> //.
Qed.

Lemma inductive_implies_semantic_sort_wf cmp ls lt
  : wf_lang ls -> wf_lang lt -> preserving_compiler lt cmp ls ->
    sort_wf_preserving_sem cmp ls lt
with inductive_implies_semantic_term_wf cmp ls lt
  : wf_lang ls -> wf_lang lt -> preserving_compiler lt cmp ls ->
    term_wf_preserving_sem cmp ls lt
with inductive_implies_semantic_args_wf cmp ls lt
  : wf_lang ls -> wf_lang lt -> preserving_compiler lt cmp ls ->
    args_wf_preserving_sem cmp ls lt
with inductive_implies_semantic_ctx_wf cmp ls lt
  : wf_lang ls -> wf_lang lt -> preserving_compiler lt cmp ls ->
    ctx_wf_preserving_sem cmp ls lt
with inductive_implies_semantic_sort_le cmp ls lt
  : wf_lang ls -> wf_lang lt -> preserving_compiler lt cmp ls ->
    sort_le_preserving_sem cmp ls lt
with inductive_implies_semantic_term_le cmp ls lt
  : wf_lang ls -> wf_lang lt -> preserving_compiler lt cmp ls ->
    term_le_preserving_sem cmp ls lt
with inductive_implies_semantic_args_le cmp ls lt
  : wf_lang ls -> wf_lang lt -> preserving_compiler lt cmp ls ->
    args_le_preserving_sem cmp ls lt.
Proof.
  all: intros wfs wft pc c.
  {
    intros t.    
    case; intros; simpl.
    pose in_cmp := i; eapply in_preserving_sort in in_cmp; destruct in_cmp as [e H]; eauto.
    erewrite named_list_all_fresh_lookup; eauto using preserving_compiler_fresh.
    simpl.
    eapply mono_subst_wf_sort; auto. 
    { eapply preserving_sort_case_inv; eauto. }
    {
      eapply inductive_implies_semantic_ctx_wf; [| |eauto |]; eauto with judgment.
    }
    {
      replace (map fst c') with (map fst (compile_ctx cmp c')).
      apply wf_subst_from_wf_args.
      eapply inductive_implies_semantic_args_wf;  [| |eauto |]; eauto with judgment.
      admit(* TODO: lemma*).
    }
    {
      eauto using preserving_compiler_all_fresh, wf_lang_all_fresh.
    }
  }
  {
    intros e t.
    case; intros; simpl.
    {
       pose in_cmp := i; eapply in_preserving_term in in_cmp; destruct in_cmp as [e' H]; eauto.
       erewrite named_list_all_fresh_lookup; eauto using preserving_compiler_fresh.
       simpl.
       rewrite compile_sort_subst.
       rewrite -with_names_from_zip.
       rewrite -compile_with_names_from.
       eapply mono_subst_wf_term; eauto. 
       { admit (*TODO: term version eapply preserving_sort_case_inv; eauto.*). }
       {
         eapply inductive_implies_semantic_ctx_wf; [| |eauto |]; eauto.
         apply rule_in_wf in i; auto.
         inversion i; subst; eauto.
       }
       {
         admit(*
         rewrite compile_subst_compile_args.
         apply wf_subst_from_wf_args.
         eapply inductive_implies_semantic_args_wf;  [| |eauto |]; eauto with judgment.
         admitTODO: lemma*).
       }
       {
         eauto using preserving_compiler_all_fresh, wf_lang_all_fresh.
       }
    }
    {
      eapply wf_term_conv.
      { eapply inductive_implies_semantic_sort_wf; [| |eauto |]; eauto. }
      { eapply inductive_implies_semantic_term_wf; [| |eauto |]; eauto. }
      { eapply inductive_implies_semantic_sort_le; [| |eauto |]; eauto. }
    }
    {
      constructor; eauto.
      by apply compile_ctx_in.
    }
  }
  {
    intro_to wf_args; case; simpl; constructor.
    { by apply fresh_compile_ctx. }
    { eapply inductive_implies_semantic_args_wf; [| |eauto |]; eauto. }
    { eapply inductive_implies_semantic_sort_wf; [| |eauto |]; eauto. }
    {
      rewrite -compile_with_names_from.
      rewrite -compile_sort_subst.
      eapply inductive_implies_semantic_term_wf; [| |eauto |]; eauto.
      rewrite with_names_from_zip.
      rewrite compile_ctx_fst.
      rewrite -with_names_from_zip.
      done.
    }
  }
  {
    intro_to wf_ctx; case; simpl; constructor.
    { by apply fresh_compile_ctx. }
    { eapply inductive_implies_semantic_ctx_wf; [| |eauto |]; eauto. }
    { eapply inductive_implies_semantic_sort_wf; [| |eauto |]; eauto. }
  }
  {
    intro_to le_sort; case; simpl; intros.
    {
      admit (*TODO: inversion lemma*).
    }
    {
      rewrite !compile_sort_subst.
      eapply le_sort_subst.
      { admit (*TODO: le subst,not leargs?
                eapply inductive_implies_semantic_subst_le; [| |eauto |]; eauto.*). }
      { eapply inductive_implies_semantic_sort_le; [| |eauto |]; eauto. }
    }
    { eapply le_sort_refl. }
    { eapply le_sort_trans.
      { eapply inductive_implies_semantic_sort_le; [| |eauto |]; eauto. }
      { eapply inductive_implies_semantic_sort_le; [| |eauto |]; eauto. }
    }
    {
      eapply le_sort_sym.
      { eapply inductive_implies_semantic_sort_le; [| |eauto |]; eauto. }
    }
  }
  {
    intro_to le_term; case; simpl; intros.
    {
      rewrite !compile_sort_subst.
      rewrite !compile_term_subst.
      eapply le_term_subst.
      { admit (*TODO: le subst,not leargs?
                eapply inductive_implies_semantic_subst_le; [| |eauto |]; eauto.*). }
      { eapply inductive_implies_semantic_term_le; [| |eauto |]; eauto. }
    }
    
    {
      admit (*TODO: inversion lemma*).
    }
    { eapply le_term_refl. }
    { eapply le_term_trans.
      { eapply inductive_implies_semantic_term_le; [| |eauto |]; eauto. }
      { eapply inductive_implies_semantic_term_le; [| |eauto |]; eauto. }
    }
    {
      eapply le_term_sym.
      { eapply inductive_implies_semantic_term_le; [| |eauto |]; eauto. }
    }
    {
      eapply le_term_conv.
      { eapply inductive_implies_semantic_sort_le; [| |eauto |]; eauto. }
      { eapply inductive_implies_semantic_term_le; [| |eauto |]; eauto. }
    }
  }
  {
    intro_to le_args; case; simpl; intros; constructor.
    { eapply inductive_implies_semantic_args_le; [| |eauto |]; eauto. }
    { by apply fresh_compile_ctx. }
    {
      rewrite -compile_with_names_from.
      rewrite -compile_sort_subst.
      eapply inductive_implies_semantic_term_le; [| |eauto |]; eauto.
      rewrite with_names_from_zip.
      rewrite compile_ctx_fst.
      rewrite -with_names_from_zip.
      done.
    }
  }
Admitted.
  
        
    

Lemma inductive_implies_semantic cmp ls lt
  : wf_lang ls -> wf_lang lt ->
    preserving_compiler lt cmp ls ->
    semantics_preserving cmp ls lt.
Proof.
  intros.
  repeat split.
  by eapply inductive_implies_semantic_sort_wf.
  by eapply inductive_implies_semantic_term_wf.
  by eapply inductive_implies_semantic_args_wf.
  by eapply inductive_implies_semantic_sort_le.
  by eapply inductive_implies_semantic_term_le.
  by eapply inductive_implies_semantic_args_le.
Qed.

(*
Lemma semantic_implies_inductive cmp ls lt
  : wf_lang ls -> wf_lang lt ->
    semantics_preserving cmp ls lt ->
    preserving_compiler lt cmp ls.
Proof.
  (* TODO: actually quite non-trivial *)
*)
*)
