Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From excomp Require Import Utils Syntax.

(*TODO: decide how to handle projections
TODO: write down use for projections
*) 
Inductive le_sort l c : sort_le -> sort -> sort -> Prop :=
| le_sort_by : forall n c' t1 t2 ps s1 s2,
    is_nth_level l n (sort_le_rule c' t1 t2) ->
    le_subst l c ps s1 s2 c' ->
    le_sort l c (sle n ps) t1[/s1/] t2[/s2/]
| le_sort_refl : forall n c' ps s1 s2,
    is_nth_level l n (sort_rule c') ->
    le_subst l c ps s1 s2 c' ->    
    le_sort l c (sle n ps) (srt n s1) (srt n s2)
(*| le_sort_trans : forall sp1 sp2 t1 t12 t2,
    le_sort l c sp1 t1 t12 ->
    le_sort l c sp2 t12 t2 ->
    le_sort l c (sle_trans sp1 sp2) t1 t2*)
with le_term l c : term_le -> term -> term -> sort -> Prop :=
| le_term_by : forall n c' e1 e2 t ps s1 s2,
    is_nth_level l n (term_le_rule c' e1 e2 t) ->
    le_subst l c ps s1 s2 c' ->
    le_term l c (tle n ps) e1[/s1/] e2[/s2/] t[/s2/]
| le_term_var : forall x t,
    is_nth_level c x t ->
    le_term l c (tle_var x) (var x) (var x) t
| le_term_con : forall n c' t ps s1 s2,  
    is_nth_level l n (term_rule c' t) ->
    le_subst l c ps s1 s2 c' ->    
    le_term l c (tle n ps) (con n s1) (con n s2) t[/s2/]
(* TODO: do I want transitivity as a constructor?
 I could probably get uniqueness of proofs if I used successive convs *)
(*| le_term_trans : forall p1 p2 e1 e12 e2 t,
    le_term l c p1 e1 e12 t ->
    le_term l c p2 e12 e2 t ->
    le_term l c (tle_trans p1 p2) e1 e2 t*)
(* Conversion:

c |- e1 < e2 : t  ||
               /\ ||
c |- e1 < e2 : t' \/
*)
| le_term_conv : forall sp p e1 e2 t t',
    le_term l c p e1 e2 t ->
    le_sort l c sp t t' ->
    le_term l c (tle_conv sp p) (conv sp e1) (conv sp e2) t'
with le_subst l c : subst_le -> subst -> subst -> ctx -> Prop :=
| le_subst_nil : le_subst l c [::] [::] [::] [::]
| le_subst_cons : forall pf pfs s1 s2 c' e1 e2 t,
    (* a bit of a hack to avoid mutual dependence *)
    le_sort l c' (sort_to_refl t) t t ->
    le_subst l c pfs s1 s2 c' ->
    le_term l c pf e1 e2 t[/s2/] ->
    (*choosing s1 would be a strictly stronger premise,
     but this suffices since t[/s1/] <# t[/s2/] *)
    le_subst l c (pf::pfs) (e1::s1) (e2::s2) (t::c').

Inductive wf_sort l c : sort -> Prop :=
| wf_sort_by : forall n s c',
    is_nth_level l n (sort_rule c') ->
    wf_subst l c s c' ->
    wf_sort l c (srt n s)
with wf_term l c : term -> sort -> Prop :=
| wf_term_by : forall n s c' t,
    is_nth_level l n (term_rule c' t) ->
    wf_subst l c s c' ->
    wf_term l c (con n s) t[/s/]
(* terms can be lifted to greater (less precise) types,
   but not the other way around; TODO: change the direction from le to ge? might be more intuitive
 *)
| wf_term_conv : forall e t pf t',
    wf_term l c e t ->
    le_sort l c pf t t' ->
    wf_term l c (conv pf e) t'
| wf_term_var : forall n t,
    is_nth_level c n t ->
    wf_term l c (var n) t
with wf_subst l c : subst -> ctx -> Prop :=
| wf_subst_nil : wf_subst l c [::] [::]
| wf_subst_cons : forall s c' e t,
    wf_subst l c s c' ->
    wf_sort l c' t ->
    wf_term l c e t[/s/] ->
    wf_subst l c (e::s) (t::c').

Inductive wf_ctx l : ctx -> Prop :=
| wf_ctx_nil : wf_ctx l [::]
| wf_ctx_cons : forall c v,
    wf_ctx l c ->
    wf_sort l c v ->
    wf_ctx l (v::c).

Variant wf_rule l : rule -> Prop :=
| wf_sort_rule : forall c,
    wf_ctx l c ->
    wf_rule l (sort_rule c)
| wf_term_rule : forall c t,
    wf_ctx l c ->
    wf_sort l c t ->
    wf_rule l (term_rule c t)
| le_sort_rule : forall c t1 t2,
    wf_ctx l c ->
    wf_sort l c t1 ->
    wf_sort l c t2 ->
    wf_rule l (sort_le_rule c t1 t2)
| le_term_rule : forall c e1 e2 t,
    wf_ctx l c ->
    wf_sort l c t ->
    wf_term l c e1 t ->
    wf_term l c e2 t ->
    wf_rule l (term_le_rule c e1 e2 t).

Inductive wf_lang : lang -> Prop :=
| wf_lang_nil : wf_lang [::]
| wf_lang_cons : forall l r, wf_lang l -> wf_rule l r -> wf_lang (r::l).

(* build a database of presuppositions and judgment facts *)
Create HintDb judgment discriminated.
Hint Constructors wf_sort le_sort
     wf_term le_term
     wf_subst le_subst
     wf_ctx wf_rule wf_lang : judgment.

Scheme le_sort_ind' := Minimality for le_sort Sort Prop
  with le_term_ind' := Minimality for le_term Sort Prop
  with le_subst_ind' := Minimality for le_subst Sort Prop.

Combined Scheme le_judgment_ind from le_sort_ind', le_term_ind', le_subst_ind'.

Scheme wf_sort_ind' := Minimality for wf_sort Sort Prop
  with wf_term_ind' := Minimality for wf_term Sort Prop
  with wf_subst_ind' := Minimality for wf_subst Sort Prop.

Combined Scheme wf_judgment_ind from wf_sort_ind', wf_term_ind', wf_subst_ind'.

(* Basic properties of relations *)
Lemma le_refl l c
  : (forall t, wf_sort l c t -> le_sort l c (sort_to_refl t) t t)
    /\ (forall e t, wf_term l c e t -> le_term l c (term_to_refl e) e e t)
    /\ (forall s c', wf_subst l c s c' -> le_subst l c (subst_to_refl s) s s c').
Proof using .
  move: c; eapply wf_judgment_ind;
    simpl; intros; eauto with judgment.
Qed.

Definition le_sort_reflexive l c := proj1 (le_refl l c).
Hint Immediate le_sort_reflexive : judgment.
Definition le_term_reflexive l c := proj1 (proj2 (le_refl l c)).
Hint Immediate le_term_reflexive : judgment.
Definition le_subst_reflexive l c := proj2 (proj2 (le_refl l c)).
Hint Immediate le_subst_reflexive : judgment.

Lemma is_nth_level_suffix {A: eqType} l n (a : A) l' : is_nth_level l n a -> is_nth_level (l'++l) n a.
Proof using .
  unfold is_nth_level.
  rewrite size_cat.
  case nlt: (n < size l); simpl; auto.
  move /eqP <-.
  apply /andP; split; first by apply ltn_addl.
  apply /eqP.
  rewrite -addnBA; try assumption.
  generalize (size l - n.+1).
  elim: l'; simpl; eauto.
Qed.

Hint Resolve is_nth_level_suffix : judgment.

(* Monotonicity under language extension *)
Lemma le_mono_lang l' l c
  : (forall sp t1 t2, le_sort l c sp t1 t2 -> le_sort (l'++l) c sp t1 t2)
    /\ (forall p e1 e2 t, le_term l c p e1 e2 t -> le_term (l'++l) c p e1 e2 t)
    /\ (forall ps s1 s2 c', le_subst l c ps s1 s2 c' -> le_subst (l'++l) c ps s1 s2 c').
Proof using .
  move: c; eapply le_judgment_ind; intros; eauto with judgment.
Qed.

Definition le_sort_mono_lang l' l c := proj1 (le_mono_lang l' l c).
Hint Resolve le_sort_mono_lang : judgment.

Definition le_term_mono_lang l' l c := proj1 (proj2 (le_mono_lang l' l c)).
Hint Resolve le_term_mono_lang : judgment.

Definition le_subst_mono_lang l' l c := proj2 (proj2 (le_mono_lang l' l c)).
Hint Resolve le_subst_mono_lang : judgment.

Lemma wf_mono_lang l' l c
  : (forall t, wf_sort l c t -> wf_sort (l'++l) c t)
    /\ (forall e t, wf_term l c e t -> wf_term (l'++l) c e t)
    /\ (forall s c', wf_subst l c s c' -> wf_subst (l'++l) c s c').
Proof using .
  move: c; eapply wf_judgment_ind; intros; eauto with judgment.
Qed.

Definition wf_sort_mono_lang l' l c := proj1 (wf_mono_lang l' l c).
Hint Resolve wf_sort_mono_lang : judgment.

Definition wf_term_mono_lang l' l c := proj1 (proj2 (wf_mono_lang l' l c)).
Hint Resolve wf_term_mono_lang : judgment.

Definition wf_subst_mono_lang l' l c := proj2 (proj2 (wf_mono_lang l' l c)).
Hint Resolve wf_subst_mono_lang : judgment.

Lemma wf_ctx_mono_lang l' l c : wf_ctx l c -> wf_ctx (l' ++ l) c.
Proof using .
  elim; eauto with judgment.
Qed.
Hint Resolve wf_ctx_mono_lang : judgment.

Lemma wf_rule_mono_lang l' l r : wf_rule l r -> wf_rule (l' ++ l) r.
Proof using .
  inversion; eauto 7 with judgment.
Qed.
Hint Resolve wf_rule_mono_lang : judgment.

(* Substitution preserves relations *)
Lemma le_subst_preserves l c ps s1 s2 c'
  : (forall sp t1 t2, le_sort l c' sp t1 t2 ->
                      le_subst l c ps s1 s2 c' -> le_sort l c sp[/ps/] t1[/s1/] t2[/s2/])
    /\ (forall p e1 e2 t, le_term l c' p e1 e2 t ->
                          le_subst l c ps s1 s2 c' -> le_term l c p[/ps/] e1[/s1/] e2[/s2/] t[/s2/])
    /\ (forall ps' s1' s2' c'', le_subst l c' ps' s1' s2' c'' ->
                                le_subst l c ps s1 s2 c' -> le_subst l c ps'[/ps/] s1'[/s1/] s2'[/s2/] c'').
Proof using .
  move: c'; eapply le_judgment_ind; intros; rewrite ?successive_subst_cmp; eauto with judgment.
  eapply le_sort_by; by eauto with judgment.
  eapply le_sort_refl; by eauto with judgment.
  eapply le_term_by; by eauto with judgment.
  {
    simpl.
    give_up(*TODO: lemma*).
  }
  eapply le_term_con; by eauto with judgment.
  eapply le_term_conv; by eauto with judgment.
  


    
    eapply le_sort_trans; eauto with judgment.
    fold sort_le_subst.
    Non-trivial! due to ordering & transitivity interaction
    substitution for transitivity proofs is wrong; need to put refl on one side; does that fix the issue?
    Solutions: 1. ditch transitivity in term_le, construct cast chain from transitive closures
    2. lemma about refl subst first?
Qed.

Definition le_sort_mono_lang l' l c := proj1 (le_mono_lang l' l c).
Hint Resolve le_sort_mono_lang : judgment.

Definition le_term_mono_lang l' l c := proj1 (proj2 (le_mono_lang l' l c)).
Hint Resolve le_term_mono_lang : judgment.

Definition le_subst_mono_lang l' l c := proj2 (proj2 (le_mono_lang l' l c)).
Hint Resolve le_subst_mono_lang : judgment.

Lemma wf_mono_lang l' l c
  : (forall t, wf_sort l c t -> wf_sort (l'++l) c t)
    /\ (forall e t, wf_term l c e t -> wf_term (l'++l) c e t)
    /\ (forall s c', wf_subst l c s c' -> wf_subst (l'++l) c s c').
Proof using .
  move: c; eapply wf_judgment_ind; intros; eauto with judgment.
Qed.

Definition wf_sort_mono_lang l' l c := proj1 (wf_mono_lang l' l c).
Hint Resolve wf_sort_mono_lang : judgment.

Definition wf_term_mono_lang l' l c := proj1 (proj2 (wf_mono_lang l' l c)).
Hint Resolve wf_term_mono_lang : judgment.

Definition wf_subst_mono_lang l' l c := proj2 (proj2 (wf_mono_lang l' l c)).
Hint Resolve wf_subst_mono_lang : judgment.

Lemma wf_ctx_mono_lang l' l c : wf_ctx l c -> wf_ctx (l' ++ l) c.
Proof using .
  elim; eauto with judgment.
Qed.
Hint Resolve wf_ctx_mono_lang : judgment.




Lemma decompose_in {A : eqType} l (a : A) : a \in l -> exists l1 l2, l = l1 ++ a::l2.
Admitted.

Lemma wf_lang_suffix l l' : wf_lang (l'++l) -> wf_lang l.
Proof using .
  elim: l'; simpl; auto.
  intro_to wf_lang; inversion;
  eauto with judgment.
Qed.

Lemma rule_nth_level_wf l n r : wf_lang l -> is_nth_level l n r -> wf_rule l r.
  intro wfl.
  move /is_nth_level_in.
  move /decompose_in.
  move => [l1 [l2]] rr.
  move: rr wfl => ->.
  move /wf_lang_suffix; inversion; subst.
  rewrite -cat_rcons.
  eauto with judgment.
Qed.

Lemma le_left_wf l c
  : wf_lang l ->
    (forall sp t1 t2, le_sort l c sp t1 t2 -> wf_sort l c t1)
    /\ (forall p e1 e2 t, le_term l c p e1 e2 t -> wf_term l c e1 t)
    /\ (forall ps s1 s2 c', le_subst l c ps s1 s2 c' -> wf_subst l c s1 c').
Proof using .
  intro.
  move: c; eapply le_judgment_ind; eauto with judgment.
  {
    intro_to is_true; move /rule_nth_level_wf => irwf.
    move: H => /irwf rwf.
    TODO: need mono_subst
    
Qed.

(* output contexts are well-formed *)
Lemma le_subst_ctx_out l c pfs s1 s2 c'
  : le_subst l c pfs s1 s2 c' -> wf_ctx l c'.
Proof using .
  elim; constructor; auto with judgment.
  TODO: need if le, wf
  
Hint Immediate le_subst_ctx_out : judgment.

Lemma wf_subst_ctx_out l c s c' : wf_subst l c s c' -> wf_ctx l c'.
Proof using . by inversion. Qed.
Hint Immediate wf_subst_ctx_out : judgment.


(* Presuppositions of sort well-formedness *)
Lemma le_sort_sort_l l c sp t1 t2
  : le_sort l c sp t1 t2 -> wf_sort l c t1.
Proof using . by inversion. Qed.
Hint Immediate le_sort_sort_l : judgment.

Lemma le_sort_sort_r l c sp t1 t2
  : le_sort l c sp t1 t2 -> wf_sort l c t2.
Proof using . by inversion. Qed.
Hint Immediate le_sort_sort_r : judgment.

Lemma wf_term_sort l c e t : wf_term l c e t -> wf_sort l c t.
Proof using . by inversion. Qed.
Hint Immediate wf_term_sort : judgment.

Lemma le_term_sort l c p e1 e2 t
  : le_term l c p e1 e2 t -> wf_sort l c t.
Proof using . by inversion. Qed.
Hint Immediate le_term_sort : judgment.


(* Presuppositions of term well-formedness *)
Lemma le_term_term_l l c p e1 e2 t
  : le_term l c p e1 e2 t -> wf_term l c e1 t.
Proof using . inversion; try done. Qed.
Hint Immediate le_term_term_l : judgment.

Lemma le_term_term_r l c p e1 e2 t
  : le_term l c p e1 e2 t -> wf_term l c e2 t.
Proof using . by inversion. Qed.
Hint Immediate le_term_term_r : judgment.


(* Presuppositions of subst well-formedness *)
Lemma le_subst_subst_l l c p s1 s2 c'
  : le_subst l c p s1 s2 c' -> wf_subst l c s1 c'.
Proof using . by inversion. Qed.
Hint Immediate le_subst_subst_l : judgment.

Lemma le_subst_subst_r l c p s1 s2 c'
  : le_subst l c p s1 s2 c' -> wf_subst l c s2 c'.
Proof using . by inversion. Qed.
Hint Immediate le_subst_subst_r : judgment.

Scheme le_sort_ind' := Minimality for le_sort Sort Prop
  with le_subst_ind' := Minimality for le_subst Sort Prop
  with le_term_ind' := Minimality for le_term Sort Prop
  with wf_sort_ind' := Minimality for wf_sort Sort Prop
  with wf_subst_ind' := Minimality for wf_subst Sort Prop
  with wf_term_ind' := Minimality for wf_term Sort Prop
  with wf_ctx_ind' := Minimality for wf_ctx Sort Prop
  with wf_rule_ind' := Minimality for wf_rule Sort Prop
  with wf_lang_ind' := Minimality for wf_lang Sort Prop.

Combined Scheme ind from
         le_sort_ind',
         le_subst_ind',
         le_term_ind',
         wf_sort_ind',
         wf_subst_ind',
         wf_term_ind',
         wf_ctx_ind',
         wf_rule_ind',
         wf_lang_ind'.

(* decideable typechecking *)

Import PartialCompMonad.

(*TODO: implement option ver. *)
Parameter nth_level : forall {A : Type}, seq A -> nat -> option A.
(*TODO: check should be an option I think*)

(* TODO: differentiate out of fuel? or just calculate enough? or use Function w/ measure? *)

(*TODO: assuming a partial nthlevel fn*)
(* TODO: termination? use fuel? should be structural if done right *)
Fixpoint type_wf_sort l c (t : sort) {struct t} : partial_comp unit :=
  let (n, s) := t in
  do sort_rule c' <%- nth_level l n;
  do tt <- type_wf_subst l c s c';
  ret tt
with type_le_sort l (c : ctx) pf {struct pf} : partial_comp (sort * sort) :=
       match pf with
       | sle_by n ps =>
         do sort_le_rule c' t1 t2 <%- nth_level l n;
         do (s1, s2) <- type_le_subst l c ps c';
         ret (t1[/s1/], t2[/s2/])
       | sle_refl n ps =>
         do sort_rule c' <%- nth_level l n;
         do (s1, s2) <- type_le_subst l c ps c';
         ret (srt n s1, srt n s2)
       | sle_trans p1 p2 =>
         do (t1, t12) <- type_le_sort l c p1;
         do (t12', t2) <- type_le_sort l c p2;
         do tt <- check (t12 == t12');
         ret (t1, t2)
       end
with type_wf_term l c e {struct e} : partial_comp sort :=
       match e with
       | con n s =>
         do term_rule c' t <%- nth_level l n;
         do tt <- type_wf_subst l c s c';
         ret t[/s/]
       | conv pf e' =>
         do t <- type_wf_term l c e';
         do (t1,t2) <- type_le_sort l c pf;
         do tt <- check (t == t1);
         ret t2
       | var n =>
         do e <%- nth_level c n;
         ret e
       end
with type_le_term l c pf {struct pf} : partial_comp (term * term * sort) :=
       match pf with
       | tle_by n ps =>
         do term_le_rule c' e1 e2 t <%- nth_level l n;
         do (s1, s2) <- type_le_subst l c ps c';
         ret (e1[/s1/], e2[/s2/], t[/s2/])
       | tle_refl_var x =>
         do t <%- nth_level c x;
         ret (var x, var x, t)
       | tle_refl_con n ps =>
         do term_rule c' t <%- nth_level l n;
         do (s1, s2) <- type_le_subst l c ps c';
         ret (con n s1, con n s2, t[/s2/])
       | tle_trans p1 p2 =>
         do (e1, e12, t) <- type_le_term l c p1;
         do (e12', e2, t') <- type_le_term l c p2;
         do tt <- check (t == t');
         do tt <- check (e12 == e12');
         ret (e1, e2, t)
       | tle_conv sp p =>
         do (t1, t2) <- type_le_sort l c sp;
         do (e1, e2, t1') <- type_le_term l c p;
         do _ <- check (t1 == t1');
         ret (conv sp e1, conv sp e2, t2)
       end
(* output context not easily inferred; has to be an argument *)
with type_wf_subst l c s (c' : ctx) : partial_comp unit :=
       match s, c' with
       | [::], [::] => ret tt
       | e::s', t::c'' =>
         do tt <- type_wf_sort l c' t;
         do t' <- type_wf_term l c e;
         do tt <- check (t' == t[/s'/]);
         type_wf_subst l c s' c''
       | _,_ => fail
       end
with type_le_subst l c ps (c' : ctx) : partial_comp (subst * subst) :=
       match ps, c' with
       | [::], [::] => ret ([::],[::])
       | p::ps', t::c'' =>
         do (e1, e2, t') <- type_le_term l c p;
         do (s1,s2) <- type_le_subst l c ps' c'';
         do tt <- check (t' == t[/s2/]);
         ret (e1::s1, e2::s2)
       | _, _ => fail
       end.

with type_wf_ctx l c : partial_comp unit := fail   (*TODO: assume input ctx wf everywhere*)                                                           
(*with check_wf_lang l : option unit := None TODO*).
