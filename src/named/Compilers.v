
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
  case: c1; case: c2; simpl; eauto.
Admitted.

Definition compiler_case_eqMixin := Equality.Mixin eq_compiler_caseP.

Canonical compiler_case_eqType := @Equality.Pack compiler_case compiler_case_eqMixin.

(* each element is the map for that constructor *)
Definition compiler := named_list compiler_case. 


Fixpoint compile_term (cmp : compiler) (e : exp) : exp :=
  match e with
  | var x => var x
  | con n s =>
    let default := sort_case [::] (srt "ERR" [::]) in
    let arg_terms := map (compile_term cmp) s in
    match named_list_lookup default cmp n with
    | term_case args c_case => c_case[/zip args arg_terms /]
    | _ => con "ERR"%string [::]
    end
  end.

Definition compile_args cmp := map (compile_term cmp).

Definition compile_sort (cmp : compiler) (e : sort) : sort :=
  match e with
  | srt n s =>
    let default := term_case [::] (con "ERR" [::]) in
    let arg_terms := compile_args cmp s in
    match named_list_lookup default cmp n with
    | sort_case args c_case => c_case[/zip args arg_terms/]
    | _ => srt"ERR"%string [::]
    end
  end.

Definition compile_subst (cmp : compiler) (e : subst) : subst :=
  map (fun p => (fst p, compile_term cmp (snd p))) e.

Definition compile_ctx (cmp : compiler) (e : ctx) : ctx :=
  map (fun p => (fst p, compile_sort cmp (snd p))) e.

(* TODO: ICompilers*)

(*TODO: necessary? 
 make inductive instead if so
Fixpoint wf_cmp_subst tgt_l tgt_s cmp src_c :=
  match tgt_s, src_c with
  | [::],[::] => True
  | e::s', t::c' =>
    wf_cmp_subst tgt_l s' cmp c'
    /\ wf_term tgt_l [::] e (compile cmp s' t)
  | _,_ => False
  end.

 Conjecture : wf_ctx src_l c -> 
           wf_cmp_subst l s cmp c <-> wf_subst l [::] s (map (compile cmp s) c))*)

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
  intros c0 n t0 nin.
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

(*
Lemma in_lang_in_cmp_sort lt cmp ls n c
  : preserving_compiler lt cmp ls ->
    (n, sort_rule c) \in ls ->
    exists f, (forall d, named_list_lookup d cmp n = sort_case f)
              /\ (forall s, wf_args lt [::] s
                                    (compile_ctx cmp c) ->
               wf_sort lt [::] (f s)). 
Proof.
Admitted.
*)

(*TODO: move to core*)

Lemma with_names_from_nil_r c : with_names_from c [::] = [::].
Proof.
  case: c; simpl; auto; case; auto.
Qed.



Ltac f_equal_match :=
  match goal with
  | [|- match ?e with _ => _ end = match ?e with _ => _ end]
    => let e':= fresh in remember e as e'; destruct e'
  end.
  
Lemma lookup_in_tail c c' n t s s'
    : let cs' := with_names_from (c'++ c) (s' ++ s) in
    size s == size c ->
    size s' == size c' ->
    named_list_all_fresh (c' ++ c) ->
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


(*
(* TODO: use ws_term instead? *)
Lemma strengthen_compile_term l c' c cmp s' s e t
  : wf_term l c e t ->
    let cc := compile_ctx cmp in
    let cce := compile_term cmp in
    let cs' := with_names_from (c'++ c) (s' ++ s) in
    size s == size c ->
    size s' == size c' ->
    named_list_all_fresh (c' ++ c) ->
    compile_term cmp e =  e
with strengthen_compile_args l c' c cmp s' s s1 c1
  : wf_args l c s1 c1 ->
    let cc := compile_ctx cmp in
    let cca sub := map (compile_term cmp sub) in
    let cs' := with_names_from (c'++ c) (s' ++ s) in
    size s == size c ->
    size s' == size c' ->
    named_list_all_fresh (c' ++ c) ->
    cca cs' s1 = cca (with_names_from c s) s1.
Proof using .
  all: inversion; subst; simpl; eauto.
  {
    intros; f_equal_match; auto.
    f_equal.
    eauto.
  }
  {
    intros.
    eapply lookup_in_tail; eauto.
  }
  {
    intros; f_equal; eauto.
  }
Qed.
  
Lemma strengthen_compile_sort l c' c cmp s' s t
  : wf_sort l c t ->
    let cc := compile_ctx cmp in
    let ccs := compile_sort cmp in
    let cs' := with_names_from (c'++ c) (s' ++ s) in
    size s == size c ->
    size s' == size c' ->
    named_list_all_fresh (c' ++ c) ->
    ccs cs' t = ccs (with_names_from c s) t.
Proof using .
  case.
  intros.
  simpl.
  f_equal_match; auto.
  f_equal.
  eapply strengthen_compile_args; eauto.
Qed.

Lemma named_list_all_fresh_suffix {A} (l1 l2 : named_list A)
  : named_list_all_fresh (l1 ++ l2) -> named_list_all_fresh l2.
Proof.
  elim l1; auto.
  move => [n e] l IH.
  simpl.
  move /andP => [_ H].
  by apply IH.
Qed.

Lemma strengthen_compile_ctx l c' c cmp s' s
  : 
    named_list_all_fresh cmp ->
    compile ((n, cc)::cmp) c = compile cmp c.
Proof using.
  {
    simpl.
    elim: c c' s s'; auto.
    move => [n' t'] c1 // => IH c' s s'.
    inversion; subst.
    case: s; simpl; [ easy| intros e s].
    move /eqP; case => /eqP eqss eqss'.
    intro nlaf.
    f_equal;[f_equal|].
    {
      rewrite -!cat_rcons.
      change ((n', e) :: with_names_from ?c ?s) with
          (with_names_from ((n',t')::c) (e::s)).
      change (?a::?b) with ([::a]++b).
      erewrite !strengthen_compile_sort; eauto.
      {
        change ([::?a]++?b) with (a::b).
        eapply named_list_all_fresh_suffix; eassumption.
      }
      {
        rewrite !size_rcons.
        by apply /eqP; f_equal; apply /eqP.
      }
      {
          by rewrite cat_rcons.
      }
    }
    {
      rewrite -!cat_rcons.
      change ((n', e) :: with_names_from ?c ?s) with
          (with_names_from ((n',t')::c) (e::s)).
      change (?a::?b) with ([::a]++b).
      rewrite !IH; auto.
      {
        change ([::?a]++?b) with (a::b).
        eapply named_list_all_fresh_suffix; eassumption.
      }
      
      {
        rewrite !size_rcons.
        by apply /eqP; f_equal; apply /eqP.
      }
      {
          by rewrite cat_rcons.
      }
    }
  }
Qed.
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

(*
(*TODO: move to separate file*)
(*TODO: think harder about Core lack of typing for le rel; 
c should be inferrable here/refl should use wfness constr*)
Inductive le_sort_cut (l : lang) (c : ctx) : sort -> sort -> Prop :=
| le_sort_by_cut : forall name c' t1 t2 s1 s2,
    [s> !c' |- (name) !t1 = !t2] \in l ->
    le_args_cut l c c' s1 s2 ->
    le_sort_cut l c t1[/with_names_from c' s1/] t2[/with_names_from c' s2/]
| le_sort_refl_cut : forall n c' s1 s2,
    le_args_cut l c c' s1 s2 ->
    le_sort_cut l c (srt n s1) (srt n s2)
| le_sort_trans_cut : forall t1 t12 t2,
    le_sort_cut l c t1 t12 ->
    le_sort_cut l c t12 t2 ->
    le_sort_cut l c t1 t2
| le_sort_sym_cut : forall t1 t2, le_sort_cut l c t1 t2 -> le_sort_cut l c t2 t1
with le_term_cut (l : lang) (c : ctx): sort -> exp -> exp -> Prop :=
| le_term_by_cut : forall name c' t e1 e2 s1 s2,
    [:> !c' |- (name) !e1 = !e2 : !t] \in l ->
    le_args_cut l c c' s1 s2 ->
    le_term_cut l c t[/with_names_from c' s2/]
                e1[/with_names_from c' s1/] e2[/with_names_from c' s2/]
| le_term_refl_cut : forall t n c' s1 s2,
    le_args_cut l c c' s1 s2 ->
    le_term_cut l c t[/with_names_from c' s2/]
                (con n s1) (con n s2)
| le_term_trans_cut : forall t e1 e12 e2,
    le_term_cut l c t e1 e12 ->
    le_term_cut l c t e12 e2 ->
    le_term_cut l c t e1 e2
| le_term_sym_cut : forall t e1 e2, le_term_cut l c t e1 e2 -> le_term_cut l c t e2 e1
(* Conversion:

c |- e1 < e2 : t  ||
               /\ ||
c |- e1 < e2 : t' \/
*)
| le_term_conv_cut : forall t t',
    le_sort_cut l c t t' ->
    forall e1 e2,
    le_term_cut l c t e1 e2 ->
    le_term_cut l c t' e1 e2
with le_args_cut (l : lang) (c : ctx) : ctx -> list exp -> list exp -> Prop :=
| le_args_nil_cut : le_args_cut l c [::] [::] [::]
| le_args_cons_cut : forall c' s1 s2,
    le_args_cut l c c' s1 s2 ->
    forall name t e1 e2,
      fresh name c' ->
      le_term_cut l c t[/with_names_from c' s2/] e1 e2 ->
      le_args_cut l c ((name, t)::c') (e1::s1) (e2::s2).
(*with le_subst_cut (l : lang) (c : ctx) : ctx -> subst -> subst -> Prop :=
| le_subst_nil_cut : le_subst_cut l c [::] [::] [::]
| le_subst_cons_cut : forall c' s1 s2,
    le_subst_cut l c c' s1 s2 ->
    forall name t e1 e2,
      fresh name c' ->
      le_term_cut l c t[/s2/] e1 e2 ->
    (*choosing s1 would be a strictly stronger premise,
      this suffices since t[/s1/] <# t[/s2/] *)
    le_subst_cut l c ((name, t)::c') ((name,e1)::s1) ((name,e2)::s2).*)

Lemma le_sort_cut_equiv l c t1 t2
  : le_sort l c t1 t2 <-> le_sort_cut l c t1 t2
with le_term_cut_equiv l c t e1 e2
  : le_term l c t e1 e2 <-> le_term_cut l c t e1 e2
with le_args_cut_equiv l c c' s1 s2
  : le_args l c c' s1 s2 <-> le_args_cut l c c' s1 s2.
Admitted.

Definition sort_le_preserving_sem_cut cmp l1 l2 :=
  forall s c t1 t2, wf_ctx l1 c ->
                wf_subst l2 [::] s (compile_ctx cmp s c) ->
                le_sort_cut l1 c t1 t2 ->
                le_sort l2 [::] (compile_sort cmp s t1) (compile_sort cmp s t2).

Definition term_le_preserving_sem_cut cmp l1 l2 :=
  forall s c e1 e2 t, wf_ctx l1 c ->
                wf_subst l2 [::] s (compile_ctx cmp s c) ->
                le_term_cut l1 c t e1 e2 ->
                le_term l2 [::] (compile_sort cmp s t)
                        (compile_term cmp s e1) (compile_term cmp s e2).

Definition args_le_preserving_sem_cut cmp l1 l2 :=
  forall s c s1 s2 c', wf_ctx l1 c ->
                wf_subst l2 [::] s (compile_ctx cmp s c) ->
                le_args_cut l1 c c' s1 s2 ->
                (* TODO: picking s2 here makes things interesting in a bad way *)
                le_args l2 [::] (compile_ctx cmp (with_names_from c' (map (compile_term cmp s) s2)) c')
                        (map (compile_term cmp s) s1) (map (compile_term cmp s) s2).
*)
Ltac case_match :=match goal with
  | [|- context[match ?e with _ => _ end]]
    => let e':= fresh in remember e as e'; destruct e'
  end.

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
  exact (srt "ERR" [::]).
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
  : named_list_all_fresh l ->
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
    named_list_all_fresh ls ->
    named_list_all_fresh cmp.
Proof using .
  elim; simpl; auto; intro_to is_true;
    move /andP => [frn af]; auto; apply /andP; split; auto.
  all: eapply preserving_compiler_fresh;eauto.
Qed. 

Lemma wf_lang_all_fresh l : wf_lang l -> named_list_all_fresh l.
Proof.
  elim; intros; simpl in *; auto.
  apply /andP; auto.
Qed.


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

Lemma preserving_sort_case_inv n t c lt cmp ls
  :  preserving_compiler lt cmp ls ->
     wf_lang ls ->
     (n, sort_rule c) \in ls ->
     (n, sort_case (map fst c) t) \in cmp ->
     wf_sort lt (compile_ctx cmp c) t.
Proof.
  intros pc wfl.
  suff: named_list_all_fresh ls; [intro nlfls | eapply wf_lang_all_fresh; by eauto].
  suff: named_list_all_fresh cmp; [intro nlfc| eapply preserving_compiler_all_fresh; by eauto].
  revert pc wfl nlfc nlfls.
  elim; [by cbv|..];
    intro_to wf_lang; inversion; subst; simpl;
    repeat lazymatch goal with
           | H : wf_rule _ _ |- _ => inversion H; clear H; subst
           | |- is_true(_ && _) -> _=> move /andP; case
           | |- is_true(_ == _) -> _=> move /eqP; repeat case
           | |- _ = _ -> _=> intro
           | |- is_true(_ \in _::_) -> _=> rewrite in_cons; move /orP; case
           | |- is_true(_ \in _) -> _=> intro
           | |- is_true (fresh _ _) -> _=> intro
           | |- is_true (named_list_all_fresh _) -> _=> intro
           end.
  all: try erewrite ctx_fresh_strengthen; subst; eauto; try easy.
  (* freshness contradiction *)
  all: try lazymatch goal with
      [ H : is_true (fresh ?n ?l), Hin : is_true ((?n, _) \in ?l) |- _ ] =>
      exfalso;
        suff: (n == n);
        [ apply /negP; eapply fresh_neq_in; [ exact H | exact Hin]
        | apply /eqP; reflexivity]
           end.
  all: apply rule_in_wf in b1; auto; inversion b1; done.
Qed.    


(* TODO: move to core*)
Lemma wf_subst_from_wf_args l c s c'
  :  wf_args l c s c' -> wf_subst l c (zip (map fst c') s) c'.
Proof.
  elim; simpl; constructor; eauto with judgment.
  (*with_names_from equiv*)
Admitted.


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

Lemma compile_sort_subst cmp t s
  : compile_sort cmp (t[/s/]) = (compile_sort cmp t)[/compile_subst cmp s/].
Proof.
  case: t; simpl.
  intros n a.
  rewrite (f_apply_case_map (sort_subst (compile_subst cmp s))).
  f_equal_match; simpl; auto.
Admitted.


Lemma compile_term_subst cmp e s
  : compile_term cmp (e[/s/]) = (compile_term cmp e)[/compile_subst cmp s/].
Proof.
  (* TODO: requires induction *)
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
