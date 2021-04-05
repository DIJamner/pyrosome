
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From Utils Require Import Utils BoolAsProp.
From Named Require Import Exp ARule ImCore.
Require Import String.

(* TODO: this does not admit for optimization *)
(* TODO! : trying to define compilation for to-be-inferred terms;
   how do I include info from the type?
 *)
Variant compiler_case : Set :=
| sort_case : (* target *) sort -> compiler_case
| term_case :  (* target *) exp -> compiler_case.

Definition eq_compiler_case c1 c2 : bool :=
  match c1,c2 with
  | sort_case t1, sort_case t2 => (t1 == t2)
  | term_case e1, term_case e2 => (e1 == e2)
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

Section CompilesTo.
  Context (src tgt : lang) (cmp : compiler).

  Inductive term_compiles_to : ctx -> exp -> sort -> ctx -> exp -> sort -> Prop :=
  | compile_var x c t
    : (x,t) \in c ->
      ctx_compiles_to c c' ->
      (x,t') \in c' ->
      term_compiles_to c (var x) t (var x)
  | compile_con c n s e es es' c' args t
    : (n, term_rule c' args t) \in src ->
      (n, term_case e) \in cmp ->
      (*Note: need to check wfness to get my hands on es *)
      wf_args src c s args es c' ->
      args_compile_to c es c' es' ->
      term_compiles_to c (con n s) t[/with_names_from c' es/] e[/with_names_from c' es'/]
  | compile_conv c e t t' e'
    : term_compiles_to c e t e' -> le_sort src c t t' -> term_compiles_to c e t' e'
  with args_compile_to : ctx -> list exp -> named_list sort -> list exp -> Prop :=
  | compile_nil c : args_compile_to c [::] [::] [::]
  | compile_cons c es c' es' e t e' n
    : args_compile_to c es c' es' ->
      term_compiles_to c e t[/with_names_from c' es/] e' ->
      args_compile_to c (e::es) ((n,t)::c') (e'::es')
  with sort_compiles_to : ctx -> sort -> sort -> Prop :=
  | compile_scon c n s es es' c' args t
    : (n, sort_rule c' args) \in src ->
      (n, sort_case t) \in cmp ->
      (*Note: need to check wfness to get my hands on es *)
      wf_args src c s args es c' ->
      args_compile_to c es c' es' ->
      sort_compiles_to c (scon n s) t[/with_names_from c' es'/]
  with ctx_compiles_to : ctx -> ctx -> Prop :=
  | compile_ctx_nil : ctx_compiles_to [::] [::]
  | compile_ctx_cons c c' t t' n
    : ctx_compiles_to c c' ->
      sort_compiles_to c t t' ->
      fresh n c ->
      ctx_compiles_to ((n,t)::c) ((n,t')::c').

  Inductive 

  Hint Constructors term_compiles_to args_compile_to sort_compiles_to ctx_compiles_to : imcore.


  Lemma term_compiles_is_wf c e t e'
    : term_compiles_to c e t e' -> wf_term src c e t.
  Proof.
    induction 1; eauto with imcore.
  Qed.
  Hint Resolve term_compiles_is_wf : imcore.

  (*TODO Go the other way; should rely on compiler wsness*)
  Lemma term_wf_compiles c e t
    : wf_term src c e t -> exists e', term_compiles_to c e t e'.
  Proof.
  Abort.
  
  (*TODO: move to utils*)
  Lemma subseq_nil {A:eqType} (l : list A) : subseq [::] l.
  Proof.
    destruct l; simpl; auto.
  Qed.

  Lemma args_compile_are_wf c s args es c' es'
    : args_compile_to c es c' es' ->
      size args = size s ->
      subseq (zip args s) (with_names_from c' es) ->
      wf_args src c s args es c'.
  Proof.
    intro acmp.
    revert args s.
    induction acmp; intros args s;
      destruct args; destruct s; simpl;
        let H := fresh in
        intro H; inversion H; clear H;
          let H := fresh in
          intro H; inversion H; clear H; subst; auto with imcore.
    {
      constructor; eauto with imcore.
      apply IHacmp; simpl; eauto with imcore.
      apply subseq_nil.
    }
    {
      move: H3 => /orP [ /andP [ /eqP ] |].
      {
        case; intros; subst; eauto with imcore.
      }
      {
        intros.
        constructor; eauto with imcore.
        apply IHacmp; simpl; eauto.
      }
    }
  Qed.
  Hint Resolve args_compile_are_wf : imcore.
  
  Lemma sort_compiles_is_wf c t t'
    : sort_compiles_to c t t' -> wf_sort src c t.
  Proof.
    destruct 1; eauto with imcore.
  Qed.
  Hint Resolve sort_compiles_is_wf : imcore.

  (* First we specify the properties semantically,
     then inductively on the compiler. TODO: prove equivalent
   *)
  Definition sort_wf_preserving_sem :=
    forall c c' t t', ctx_compiles_to c c' -> 
                      sort_compiles_to c t t' -> 
                      wf_sort tgt c' t'.

  Definition term_wf_preserving_sem :=
    forall c c' e e' t t', ctx_compiles_to c c' -> 
                           sort_compiles_to c t t' -> 
                           term_compiles_to c e t e' -> 
                           wf_term tgt c' e' t'.

  Definition sort_le_preserving_sem :=
    forall c c' t1 t2 t1' t2',
      ctx_compiles_to c c' -> 
      sort_compiles_to c t1 t1' -> 
      sort_compiles_to c t2 t2' -> 
      le_sort src c t1 t2 ->
      le_sort tgt c' t1' t2'.

  Definition term_le_preserving_sem :=
    forall c c' e1 e2  e1' e2' t t',
      ctx_compiles_to c c' -> 
      sort_compiles_to c t t' -> 
      term_compiles_to c e1 t e1' -> 
      term_compiles_to c e2 t e2' ->
      le_term src c t e1 e2 ->
      le_term tgt c' t' e1' e2'.

  Definition args_wf_preserving_sem :=
    forall c c' s' args es es' c2 c2',
      ctx_compiles_to c c' ->
      args_compile_to c es c2 es' ->
      ctx_compiles_to c2 c2' ->
      size args = size s' ->
      subseq (zip args s') (with_names_from c2' es') ->
      wf_args tgt c' s' args es' c2'.


  Definition args_le_preserving_sem :=
    forall c c' s1' s2' args es1 es2 es1' es2' c2 c2',
      ctx_compiles_to c c' ->
      args_compile_to c es1 c2 es1' ->
      args_compile_to c es2 c2 es2' ->
      ctx_compiles_to c2 c2' ->
      size args = size s1' ->
      subseq (zip args s1') (with_names_from c2' es1') ->
      size args = size s2' ->
      subseq (zip args s2') (with_names_from c2' es2') ->
      le_args tgt c' c2' s1' s2' args es1' es2'.

  Definition ctx_wf_preserving_sem :=
    forall c c',
      ctx_compiles_to c c' ->
      wf_ctx tgt c'.

  Definition semantics_preserving :=
    sort_wf_preserving_sem /\ term_wf_preserving_sem /\ args_wf_preserving_sem
    /\ sort_le_preserving_sem /\ term_le_preserving_sem /\ args_le_preserving_sem.


  Lemma ctx_compiles_fst c c' : ctx_compiles_to c c' -> map fst c = map fst c'.
  Proof.
    induction 1; simpl; congruence.
  Qed.
      
  Lemma fresh_compile_ctx c c' n
    : fresh n c -> ctx_compiles_to c c' -> fresh n c'.
  Proof using.
    unfold fresh; intros; erewrite <- ctx_compiles_fst; eauto.
  Qed.
  
End CompilesTo.
#[export] Hint Constructors term_compiles_to args_compile_to sort_compiles_to ctx_compiles_to : imcore.
#[export] Hint Resolve term_compiles_is_wf : imcore.
#[export] Hint Resolve args_compile_are_wf : imcore.
#[export] Hint Resolve sort_compiles_is_wf : imcore.
#[export] Hint Resolve fresh_compile_ctx : imcore.

  
(*TODO: this is an equal or stronger property (which?); includes le principles;
  formalize the relationship to those above and le semantic statements *)
(*TODO: since things aren't functions, there are quantifier issues;
  these may need some adjustment
 *)
Inductive preserving_compiler (target : lang) : lang -> compiler -> Prop :=
| preserving_compiler_nil : preserving_compiler target [::] [::]
| preserving_compiler_sort : forall src cmp n c args t,
    preserving_compiler target src cmp ->
    (forall c',
        (* Notable: only uses the previous parts of the compiler on c *)
        ctx_compiles_to src cmp c c' ->
        wf_sort target c' t) ->
    preserving_compiler target ((n,sort_rule c args) :: src) ((n, sort_case t)::cmp)
| preserving_compiler_term : forall src cmp n c args t e,
    preserving_compiler target src cmp ->
    (forall c' t',
        (* Notable: only uses the previous parts of the compiler on c,t *)
        ctx_compiles_to src cmp c c' ->
        sort_compiles_to src cmp c t t' ->
        wf_term target c' e t') ->
    preserving_compiler target ((n,term_rule c args t) :: src) ((n, term_case e)::cmp)
| preserving_compiler_sort_le : forall src cmp n c args t1 t2,
    preserving_compiler target src cmp ->
    (forall c' t1' t2',
        (* Notable: only uses the previous parts of the compiler on c,t1, t2 *)
        ctx_compiles_to src cmp c c' ->
        sort_compiles_to src cmp c t1 t1' ->
        sort_compiles_to src cmp c t2 t2' ->
        le_sort src c t1 t2 ->
        le_sort target c' t1' t2') ->
    preserving_compiler target ((n,sort_rule c args) :: src) cmp
| preserving_compiler_term_le : forall src cmp n c args t e1 e2,
    preserving_compiler target src cmp ->
    (forall c' t' e1' e2',
        (* Notable: only uses the previous parts of the compiler on c,t1, t2 *)
        ctx_compiles_to src cmp c c' ->
        sort_compiles_to src cmp c t t' ->
        term_compiles_to src cmp c e1 t e1' ->
        term_compiles_to src cmp c e2 t e2' ->
        le_term src c t e1 e2 ->
        le_term target c' t' e1' e2') ->
    preserving_compiler target ((n,sort_rule c args) :: src) cmp.
Hint Constructors preserving_compiler : imcore.



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

(*
Lemma wf_empty_term c e t : wf_ctx [::] c -> ~wf_term [::] c e t.
Proof using .
  intros wfc wft.
  elim: wft wfc; eauto.
  intros n t0 nin.
  move /wf_empty_ctx => wfe.
  move: wfe nin => ->.
  auto.  
Qed.
*)

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

(*
Local Ltac in_preserving_sort_rec :=
  intros;
      match goal with
        [ Hin : is_true(_\in_),
          IH : is_true(_\in_) -> exists t,_ |- _] =>
        move: (IH Hin); case; intros
      end; solve [eauto 3 | eexists; rewrite in_cons; apply /orP; eauto].

Lemma in_preserving_sort lt ls cmp n c' args
  : preserving_compiler lt ls cmp ->
    (n, sort_rule c' args) \in ls ->
    exists t,(n, sort_case t) \in cmp.
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

Lemma in_preserving_term lt cmp ls n c' args t
  : preserving_compiler lt cmp ls ->
    (n, term_rule c' args t) \in ls ->
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
 *)

(*
(*TODO: use existing lemmas*)
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
*)

Lemma preserving_compiler_fresh n lt ls cmp
  : preserving_compiler lt ls cmp ->
    fresh n ls ->
    fresh n cmp.
Proof using .
  unfold fresh; induction 1; simpl; auto;
    rewrite !in_cons.
  (*
  all: move /negP; intros H'.
  all: apply /negP; move /orP; intro H''.
  all: apply H'; clear H'; try apply /orP.
  all: intuition; try right; eauto.
  rewrite H1 in IHpreserving_compiler.*)
Admitted.
Hint Resolve  preserving_compiler_fresh : imcore.
  
Lemma preserving_compiler_all_fresh lt cmp ls
  : preserving_compiler lt ls cmp ->
    all_fresh ls ->
    all_fresh cmp.
Proof using .
  induction 1; simpl; auto.
  (*TODO: bool to prop utility*)
Admitted.
Hint Resolve preserving_compiler_all_fresh : judgment.

(* TODO: move to Core *)
Lemma wf_lang_all_fresh l : wf_lang l -> all_fresh l.
Proof.
  elim; intros; simpl in *; auto.
  apply /andP; auto.
Qed.
Hint Resolve wf_lang_all_fresh : judgment.

(*
Lemma term_fresh_strengthen n cc l cmp c e t
  : fresh n l ->
    wf_term l c e t ->
    compile_term ((n, cc) :: cmp) e = compile_term cmp e
with args_fresh_strengthen n cc l cmp c s args es c'
  : fresh n l ->
    wf_args l c s args es c' ->
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
Qed.  *)


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

(*
(* TODO: relate independent judgment to elab
   to port core lemmas.
*)
Parameter rule_in_wf
     : forall (l : lang) (r : rule) (n : string),
       wf_lang l -> (n, r) \in l -> wf_rule l r.

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
*)

(*
Local Ltac prove_inv_lem :=
  setup_inv_lem;
  elim; [by cbv|..];
    intros; simpl in *; break;
  repeat inv_lem_step; eauto.
*)

Lemma invert_sort_case_eq t t0
  : sort_case t = sort_case t0 <-> t = t0.
Proof. intuition; inversion H; eauto with imcore. Qed.
Hint Rewrite invert_sort_case_eq : imcore.

Lemma invert_term_case_eq t t0
  : term_case t = term_case t0 <-> t = t0.
Proof. intuition; inversion H; eauto with imcore. Qed.
Hint Rewrite invert_term_case_eq : imcore.

Lemma invert_sort_rule_eq c args c' args'
  : sort_rule c args = sort_rule c' args' <->c = c' /\ args = args'.
Proof. intuition; try inversion H; subst; eauto  with imcore. Qed.
Hint Rewrite invert_sort_rule_eq : imcore.

Lemma invert_term_rule_eq c args t c' args' t'
  : term_rule c args t = term_rule c' args' t' <-> c = c' /\ args = args' /\ t = t'.
Proof. intuition; try inversion H; subst; eauto  with imcore. Qed.
Hint Rewrite invert_term_rule_eq : imcore.

(*TODO: move to the right places*)
Lemma invert_wf_lang_cons l r n
  : wf_lang ((n,r)::l) <-> fresh n l /\ wf_rule l r /\ wf_lang l.
Proof.
  intuition; try inversion H; eauto with imcore.
Qed.
Hint Rewrite invert_wf_lang_cons : imcore.

Lemma invert_wf_sort_rule l c args
  : wf_rule l (sort_rule c args) <-> wf_ctx l c /\ subseq args (map fst c).
Proof.
  intuition; try inversion H; eauto with imcore.
Qed.
Hint Rewrite invert_wf_sort_rule : imcore.

Lemma invert_wf_term_rule l c args t
  : wf_rule l (term_rule c args t) <->
    wf_ctx l c /\ subseq args (map fst c) /\ wf_sort l c t.
Proof.
  intuition; try inversion H; eauto with imcore.
Qed.
Hint Rewrite invert_wf_term_rule : imcore.

Lemma invert_le_sort_rule l c t1 t2
  : wf_rule l (sort_le c t1 t2) <->
    wf_ctx l c /\  wf_sort l c t1 /\ wf_sort l c t2.
Proof.
  intuition; try inversion H; eauto with imcore.
Qed.
Hint Rewrite invert_le_sort_rule : imcore.

Lemma invert_le_term_rule l c e1 e2 t
  : wf_rule l (term_le c e1 e2 t) <->
    wf_ctx l c /\  wf_sort l c t
    /\ wf_term l c e1 t /\ wf_term l c e2 t.
Proof.
  intuition; try inversion H; eauto with imcore.
Qed.
Hint Rewrite invert_le_term_rule : imcore.

Lemma wf_args_lang_monotonicity_app l c al args el c' l'
  : wf_args l c al args el c' -> wf_args (l' ++ l) c al args el c'.
Proof.
  induction l'; simpl; intros; break; eauto using wf_args_lang_monotonicity.
Qed.
Hint Resolve wf_args_lang_monotonicity_app : imcore.

Lemma le_sort_lang_monotonicity_app l c t1 t2 l'
  : le_sort l c t1 t2 -> le_sort (l' ++ l) c t1 t2.
Proof.
  induction l'; simpl; intros; break; eauto using le_sort_lang_monotonicity.
Qed.  
Hint Resolve le_sort_lang_monotonicity_app : imcore.

Lemma term_compiles_to_mono c e t e' src cmp src' cmp'
  : term_compiles_to src cmp c e t e' ->
    term_compiles_to (src'++ src) (cmp'++ cmp) c e t e'.
Proof.
  induction 1; econstructor; rewrite ?mem_cat;
    autorewrite with bool_utils in *;
    eauto with imcore.
    admit.
    (*TODO: need stronger IH
    clear H H0 H1 args t.
    induction H2; simpl; eauto with imcore.
    constructor; eauto with imcore.*)
Admitted.


Lemma ctx_compiles_to_mono c c' src cmp src' cmp'
  : ctx_compiles_to src cmp c c' ->
    ctx_compiles_to (src'++ src) (cmp'++ cmp) c c'.
Admitted.
Hint Resolve ctx_compiles_to_mono : imcore.


Lemma term_compiles_to_strengthen tgt src cmp c t e e' src' cmp'
  : wf_sort src c t ->
    preserving_compiler tgt src cmp ->
    term_compiles_to (src'++src) (cmp' ++ cmp) c e t e' ->
    term_compiles_to src cmp c e t e'.
Proof.
  (*
  intro wfc; revert c'.
  induction wfc; intro c';
    let H:=fresh in intro H; inversion H; clear H; subst; constructor; eauto with imcore.*)
Admitted.

Lemma sort_compiles_to_strengthen tgt src cmp c t t' src' cmp'
  : wf_sort src c t ->
    preserving_compiler tgt src cmp ->
    sort_compiles_to (src'++src) (cmp' ++ cmp) c t t' ->
    sort_compiles_to src cmp c t t'.
Proof.
  (*
  intro wfc; revert c'.
  induction wfc; intro c';
    let H:=fresh in intro H; inversion H; clear H; subst; constructor; eauto with imcore.*)
Admitted.

Lemma ctx_compiles_to_strengthen tgt src cmp c c' src' cmp'
  : wf_ctx src c ->
    preserving_compiler tgt src cmp ->
    ctx_compiles_to (src'++src) (cmp' ++ cmp) c c' ->
    ctx_compiles_to src cmp c c'.
Proof.
  (*
  intro wfc; revert c'.
  induction wfc; intro c';
    let H:=fresh in intro H; inversion H; clear H; subst; constructor; eauto with imcore.*)
Admitted.

Ltac solve_inv_lem :=
  setup_inv_lem;
  induction 1; [ by compute |..];
    intros; simpl in *; break;
      autorewrite with bool_utils imcore in *;
      intuition; subst;
        repeat match goal with
      [H : is_true(in_once _ _ _)|- _] =>
      rewrite -all_fresh_in_once in H
      | [ H : ctx_compiles_to (?r::?l) _ _ _|-_] =>
      change (r::l) with ([::r]++l) in H
      | [ H : ctx_compiles_to _ (?r::?l) _ _|-_] =>
      change (r::l) with ([::r]++l) in H
      | [ H : ctx_compiles_to _ ?cmp _ _|-_] =>
        is_var cmp; change (cmp) with ([::] ++ cmp) in H
      | [ H : sort_compiles_to (?r::?l) _ _ _ _|-_] =>
      change (r::l) with ([::r]++l) in H
      | [ H : sort_compiles_to _ (?r::?l) _ _ _|-_] =>
      change (r::l) with ([::r]++l) in H
      | [ H : sort_compiles_to _ ?cmp _ _ _|-_] =>
        is_var cmp; change (cmp) with ([::] ++ cmp) in H
      | [ H : term_compiles_to (?r::?l) _ _ _ _ _|-_] =>
      change (r::l) with ([::r]++l) in H
      | [ H : term_compiles_to _ (?r::?l) _ _ _ _|-_] =>
      change (r::l) with ([::r]++l) in H
      | [ H : term_compiles_to _ ?cmp _ _ _ _|-_] =>
        is_var cmp; change (cmp) with ([::] ++ cmp) in H
    | [H : is_true((?n, _)\in ?cmp),
       H1 : is_true(fresh ?n ?l),
            H2 : preserving_compiler _ ?l ?cmp |-_] =>
      exfalso;
      let H' := fresh in
      pose proof (preserving_compiler_fresh H2 H1) as H';
        let H'' := fresh in
        pose proof (fresh_neq_in H' H) as H'';
          move: H'' => /eqP; tauto
    | [wfl : wf_lang ?l,
             H : is_true ((_,_)\in ?l) |- _] =>
      pose proof (rule_in_wf wfl H) as H'; inversion H'; clear H H'; subst
    end;
        eauto 7 using sort_compiles_to_strengthen,
        term_compiles_to_strengthen,
        ctx_compiles_to_strengthen with imcore.

Lemma preserving_sort_case_inv n t c c' args lt cmp ls
  :  preserving_compiler lt ls cmp ->
     wf_lang ls ->
     (n, sort_rule c args) \in ls ->
     (n, sort_case t) \in cmp ->
     ctx_compiles_to ls cmp c c' ->
     wf_sort lt c' t.
Proof using .
  solve_inv_lem.
Qed.

Lemma preserving_term_case_inv n e t t' c c' args lt cmp ls
  :  preserving_compiler lt ls cmp ->
     wf_lang ls ->
     (n, term_rule c args t) \in ls ->
     (n, term_case e) \in cmp ->
     ctx_compiles_to ls cmp c c' ->
     sort_compiles_to ls cmp c t t' ->
     wf_term lt c' e t'.
Proof using .
  solve_inv_lem.
Qed.


Lemma preserving_sort_le_inv n t1 t1' t2 t2' c c' lt cmp ls
  :  preserving_compiler lt ls cmp ->
     wf_lang ls ->
     (n, sort_le c t1 t2) \in ls ->
     ctx_compiles_to ls cmp c c' ->
     sort_compiles_to ls cmp c t1 t1' ->
     sort_compiles_to ls cmp c t2 t2' ->
     le_sort lt c' t1' t2'.
Proof using . solve_inv_lem. Qed.


Lemma preserving_term_le_inv n e1 e1' e2 e2' t t' c c' lt cmp ls
  :  preserving_compiler lt ls cmp ->
     wf_lang ls ->
     (n, term_le c e1 e2 t) \in ls ->
     ctx_compiles_to ls cmp c c' ->
     sort_compiles_to ls cmp c t t' ->
     term_compiles_to ls cmp c e1 t e1' ->
     term_compiles_to ls cmp c e2 t e2' ->
     le_term lt c' t' e1' e2'.
Proof using . solve_inv_lem. Qed.


Lemma f_apply_case_map {A B} (f : A -> B) cc b1 b2
  : f match cc with
      | sort_case c_case => b1 c_case
      | term_case c_case => b2 c_case
      end
    = match cc with
      | sort_case c_case => f (b1 c_case)
      | term_case c_case => f (b2 c_case)
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

 *)

(*
(*TODO: not true b/c not a fn!*)
Lemma compile_ctx_in ls cmp n t t' c c'
  : ctx_compiles_to ls cmp c c' ->
    (n,t) \in c ->
    sort_compiles_to ls cmp t t' ->
    (n, t') \in c'.
*)

(*
Lemma compile_ctx_fst c cmp : map fst (compile_ctx cmp c) = map fst c.
Proof.
  elim: c; auto.
  case => n s l //= -> //.
Qed.
 *)

Lemma inductive_implies_term_wf lt ls cmp
  : wf_lang ls -> wf_lang lt -> preserving_compiler lt ls cmp ->
    term_wf_preserving_sem ls lt cmp
with inductive_implies_args_wf lt ls cmp
  : wf_lang ls -> wf_lang lt -> preserving_compiler lt ls cmp ->
    args_wf_preserving_sem ls lt cmp.
Proof.
  all: intros.
  {
    unfold term_wf_preserving_sem.
    intros.
    destruct H4; simpl.
    {
      constructor.
      (*TODO: not true b/c not a fn!*)
      Lemma compile_ctx_in
    revert dependent t'.
    revert dependent c'.
    destruct H4

  
Lemma inductive_implies_semantic ls lt cmp
Proof.
  intros; unfold semantics_preserving.
  Scheme sort_wf_ind' := Minimality for wf_sort Sort Prop
  with term_wf_ind' := Minimality for wf_term Sort Prop
  with args_wf_ind' := Minimality for wf_args Sort Prop
  with sort_le_ind' := Minimality for le_sort Sort Prop
  with term_le_ind' := Minimality for le_term Sort Prop
    with args_le_ind' := Minimality for le_args Sort Prop.
  Combined Scheme judge_ind from
           sort_wf_ind',
           term_wf_ind',
           args_wf_ind',
           sort_le_ind',
           term_le_ind',
           args_le_ind'.
  repeat match goal with [|-context[?f ls lt cmp]] =>
                         unfold f end.
  simple apply judge_ind.
  : 
     

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

*)

(*Note: args not helpful*)
Fixpoint make_compiler
           (cmp_sort : string -> list string -> sort)
           (cmp_exp : string -> list string -> exp)
           (l : lang) : compiler :=
  match l with
  | (n,sort_rule c args)::l' =>
    (n,sort_case (cmp_sort n (map fst c)))
      ::(make_compiler cmp_sort cmp_exp l')
  | (n,term_rule c args _)::l' => (n,term_case (cmp_exp n (map fst c)))
      ::(make_compiler cmp_sort cmp_exp l')
  | (n,_)::l' => 
    (make_compiler cmp_sort cmp_exp l')
  | [::] => [::]
  end.
