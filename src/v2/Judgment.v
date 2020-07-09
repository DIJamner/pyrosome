Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From excomp Require Import Utils Syntax.


Inductive wf_sort : lang -> ctx -> sort -> Prop :=
| wf_sort_by : forall l c n s c',
    wf_lang l ->
    wf_ctx l c ->
    is_nth_level l n (sort_rule c') ->
    wf_subst l c s c' ->
    wf_sort l c (srt n s)
with le_sort : lang -> ctx -> sort_le -> sort -> sort -> Prop :=
| le_sort_by : forall l c n c' t1 t2 ps s1 s2,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t1[/s1/] ->
    wf_sort l c t2[/s2/] ->
    is_nth_level l n (sort_le_rule c' t1 t2) ->
    le_subst l c ps s1 s2 c' ->
    le_sort l c (sle_by n ps) t1[/s1/] t2[/s2/]
| le_sort_refl : forall l c n c' ps s1 s2,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c (srt n s1) ->
    wf_sort l c (srt n s2) ->    
    is_nth_level l n (sort_rule c') ->
    le_subst l c ps s1 s2 c' ->    
    le_sort l c (sle_refl n ps) (srt n s1) (srt n s2)
| le_sort_trans : forall l sp1 sp2 c t1 t12 t2,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t1 ->
    wf_sort l c t2 ->
    le_sort l c sp1 t1 t12 ->
    le_sort l c sp2 t12 t2 ->
    le_sort l c (sle_trans sp1 sp2) t1 t2
with wf_term : lang -> ctx -> term -> sort -> Prop :=
| wf_term_by : forall l c n s c' t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t[/s/] ->
    is_nth_level l n (term_rule c' t) ->
    wf_subst l c s c' ->
    wf_term l c (con n s) t[/s/]
(* terms can be lifted to greater (less precise) types,
   but not the other way around; TODO: change the direction from le to ge? might be more intuitive
 *)
| wf_term_conv : forall l c e t pf t',
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t' ->
    wf_term l c e t ->
    le_sort l c pf t t' ->
    wf_term l c (conv pf e) t'
| wf_term_var : forall l c n t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t ->
    is_nth_level c n t ->
    wf_term l c (var n) t
with le_term : lang -> ctx -> term_le -> term -> term -> sort -> Prop :=
| le_term_by : forall l c n c' e1 e2 t ps s1 s2,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t[/s2/] ->
    wf_term l c e1[/s1/] t[/s2/] ->
    wf_term l c e2[/s2/] t[/s2/] ->
    is_nth_level l n (term_le_rule c' e1 e2 t) ->
    le_subst l c ps s1 s2 c' ->
    le_term l c (tle_by n ps) e1[/s1/] e2[/s2/] t[/s2/]
| le_term_refl_var : forall l c x t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t ->
    wf_term l c (var x) t ->
    is_nth_level c x t ->
    le_term l c (tle_refl_var x) (var x) (var x) t
| le_term_refl_con : forall l c n c' t ps s1 s2,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t[/s2/] ->
    wf_term l c (con n s1) t[/s2/] ->
    wf_term l c (con n s2) t[/s2/] ->    
    is_nth_level l n (term_rule c' t) ->
    le_subst l c ps s1 s2 c' ->    
    le_term l c (tle_refl_con n ps) (con n s1) (con n s2) t[/s2/]
| le_term_trans : forall l p1 p2 c e1 e12 e2 t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t ->
    wf_term l c e1 t ->
    wf_term l c e2 t ->
    le_term l c p1 e1 e12 t ->
    le_term l c p2 e12 e2 t ->
    le_term l c (tle_trans p1 p2) e1 e2 t
(* Conversion:

c |- e1 < e2 : t  ||
               /\ ||
c |- e1 < e2 : t' \/
*)
| le_term_conv : forall l sp p c e1 e2 t t',
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t' ->
    wf_term l c (conv sp e1) t' ->
    wf_term l c (conv sp e2) t' ->
    le_term l c p e1 e2 t ->
    le_sort l c sp t t' ->
    le_term l c (tle_conv sp p) (conv sp e1) (conv sp e2) t'
with wf_subst : lang -> ctx -> subst -> ctx -> Prop :=
| wf_subst_nil : forall l c,
    wf_lang l ->
    wf_ctx l c ->
    wf_ctx l [::] ->
    wf_subst l c [::] [::]
| wf_subst_cons : forall l c s c' e t,
    wf_lang l ->
    wf_ctx l c ->
    wf_ctx l (t::c') ->
    wf_subst l c s c' ->
    wf_sort l c' t ->
    wf_term l c e t[/s/] ->
    wf_subst l c (e::s) (t::c')
with le_subst : lang -> ctx -> subst_le -> subst -> subst -> ctx -> Prop :=
| le_subst_nil : forall l c,
    wf_lang l ->
    wf_ctx l c ->
    wf_ctx l [::] ->
    wf_subst l c [::] [::] ->
    le_subst l c [::] [::] [::] [::]
| le_subst_cons : forall l pf pfs c s1 s2 c' e1 e2 t,
    wf_lang l ->
    wf_ctx l c ->
    wf_ctx l (t::c') ->
    wf_subst l c (e1::s1) (t::c') ->
    wf_subst l c (e2::s2) (t::c') ->
    le_subst l c pfs s1 s2 c' ->
    le_term l c pf e1 e2 t[/s2/] ->
    (*choosing s1 would be a strictly stronger premise,
     but this suffices since t[/s1/] <# t[/s2/] *)
    le_subst l c (pf::pfs) (e1::s1) (e2::s2) (t::c')
with wf_ctx : lang -> ctx -> Prop :=
| wf_ctx_nil : forall l, wf_lang l -> wf_ctx l [::]
| wf_ctx_cons : forall l c v,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c v ->
    wf_ctx l (v::c)
with wf_rule : lang -> rule -> Prop :=
| wf_sort_rule : forall l c,
    wf_lang l ->
    wf_ctx l c ->
    wf_rule l (sort_rule c)
| wf_term_rule : forall l c t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t ->
    wf_rule l (term_rule c t)
| le_sort_rule : forall l c t1 t2,
    wf_lang l -> 
    wf_ctx l c ->
    wf_sort l c t1 ->
    wf_sort l c t2 ->
    wf_rule l (sort_le_rule c t1 t2)
| le_term_rule : forall l c e1 e2 t,
    wf_lang l -> 
    wf_ctx l c ->
    wf_sort l c t ->
    wf_term l c e1 t ->
    wf_term l c e2 t ->
    wf_rule l (term_le_rule c e1 e2 t)
with wf_lang : lang -> Prop :=
| wf_lang_nil : wf_lang [::]
| wf_lang_cons : forall l r, wf_lang l -> wf_rule l r -> wf_lang (r::l).

(* database of constructor hints. In general, this should be avoided 
   in favor of the databse below of related lemmas with fewer hypotheses *)
Create HintDb judgment_constructors discriminated.
Hint Constructors wf_sort le_sort
     wf_term le_term
     wf_subst le_subst
     wf_ctx wf_rule wf_lang : judgment_constructors.

(* build a database of presuppositions and judgment facts *)
Create HintDb judgment discriminated.

(* Presuppositions of language well-formedness *)
Lemma wf_sort_lang l c t : wf_sort l c t -> wf_lang l.
Proof using . by inversion. Qed.
Hint Immediate wf_sort_lang : judgment.

Lemma le_sort_lang l c pf t1 t2 : le_sort l c pf t1 t2 -> wf_lang l.
Proof using . by inversion. Qed.
Hint Immediate le_sort_lang : judgment.

Lemma wf_term_lang l c e t : wf_term l c e t -> wf_lang l.
Proof using . by inversion. Qed.
Hint Immediate wf_term_lang : judgment.

Lemma le_term_lang l c p e1 e2 t
  : le_term l c p e1 e2 t -> wf_lang l.
Proof using . by inversion. Qed.
Hint Immediate le_term_lang : judgment.

Lemma wf_subst_lang l c s c' : wf_subst l c s c' -> wf_lang l.
Proof using . by inversion. Qed.
Hint Immediate wf_subst_lang : judgment.

Lemma le_subst_lang l c ps s1 s2 c'
  : le_subst l c ps s1 s2 c' -> wf_lang l.
Proof using . by inversion. Qed.
Hint Immediate le_subst_lang : judgment.

Lemma wf_ctx_lang l c : wf_ctx l c -> wf_lang l.
Proof using . by inversion. Qed.
Hint Immediate wf_ctx_lang : judgment.

Lemma wf_rule_lang l r : wf_rule l r -> wf_lang l.
Proof using . by inversion. Qed.
Hint Immediate wf_rule_lang : judgment.


(* Presuppositions of context well-formedness *)
Lemma wf_sort_ctx l c t : wf_sort l c t -> wf_ctx l c.
Proof using . by inversion. Qed.
Hint Immediate wf_sort_ctx : judgment.

Lemma le_sort_ctx l c pf t1 t2
  : le_sort l c pf t1 t2 -> wf_ctx l c.
Proof using . by inversion. Qed.
Hint Immediate le_sort_ctx : judgment.

Lemma wf_term_ctx l c e t : wf_term l c e t -> wf_ctx l c.
Proof using . by inversion. Qed.
Hint Immediate wf_term_ctx : judgment.

Lemma le_term_ctx l c pf e1 e2 t
  : le_term l c pf e1 e2 t -> wf_ctx l c.
Proof using . by inversion. Qed.
Hint Immediate le_term_ctx : judgment.

Lemma wf_subst_ctx_in l c s c' : wf_subst l c s c' -> wf_ctx l c.
Proof using . by inversion. Qed.
Hint Immediate wf_subst_ctx_in : judgment.

Lemma wf_subst_ctx_out l c s c' : wf_subst l c s c' -> wf_ctx l c'.
Proof using . by inversion. Qed.
Hint Immediate wf_subst_ctx_out : judgment.

Lemma le_subst_ctx_in l c pfs s1 s2 c'
  : le_subst l c pfs s1 s2 c' -> wf_ctx l c.
Proof using . by inversion. Qed.
Hint Immediate le_subst_ctx_in : judgment.

Lemma le_subst_ctx_out l c pfs s1 s2 c'
  : le_subst l c pfs s1 s2 c' -> wf_ctx l c'.
Proof using . by inversion. Qed.
Hint Immediate le_subst_ctx_out : judgment.


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
