Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From excomp Require Import Utils ProofExp ProofRule.
From excomp Require Exp Core Rule.


Inductive wf_sort : lang -> ctx -> exp -> Prop :=
| wf_sort_by : forall l c n s c',
    wf_lang l ->
    wf_ctx l c ->
    is_nth_level l n (sort_rule c') ->
    wf_subst l c s c' ->
    wf_sort l c (con n s)
with le_sort : lang -> lepf -> ctx -> exp -> exp -> Prop :=
| le_sort_by : forall l n c t1 t2,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t1 ->
    wf_sort l c t2 ->
    is_nth_level l n ({< c |- t1 <# t2})->
    le_sort l (lepf_by n) c t1 t2
| le_sort_subst : forall l pf pfs c s1 s2 c' t1' t2',
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t1'[/s1/] ->
    wf_sort l c t2'[/s2/] ->
    le_subst l pfs c s1 s2 c' ->
    le_sort l pf c' t1' t2' ->
    le_sort l (lepf_subst pf pfs) c t1'[/s1/] t2'[/s2/]
| le_sort_refl : forall l c t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t ->
    le_sort l lepf_refl c t t
| le_sort_trans : forall l pf1 pf2 c t1 t12 t2,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t1 ->
    wf_sort l c t2 ->
    le_sort l pf1 c t1 t12 ->
    le_sort l pf2 c t12 t2 ->
    le_sort l (lepf_trans pf1 pf2) c t1 t2
with wf_term : lang -> ctx -> exp -> exp -> Prop :=
| wf_term_by : forall l c n s c' t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t[/s/] ->
    is_nth_level l n ({| c' |- t}) ->
    wf_subst l c s c' ->
    wf_term l c (con n s) t[/s/]
(* terms can be lifted to greater (less precise) types,
   but not the other way around; TODO: change the direction? might be more intuitive
 *)
| wf_term_conv : forall l c e t pf t',
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t' ->
    wf_term l c e t ->
    le_sort l pf c t t' ->
    wf_term l c (conv pf e) t'
| wf_term_var : forall l c n t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t ->
    is_nth_level c n t ->
    wf_term l c (var n) t
with le_term : lang -> lepf -> ctx -> exp -> exp -> exp -> Prop :=
| le_term_subst : forall l pf pfs c s1 s2 c' e1 e2 t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t[/s2/] ->
    wf_term l c e1[/s1/] t[/s2/] ->
    wf_term l c e2[/s2/] t[/s2/] ->
    le_subst l pfs c s1 s2 c' ->
    le_term l pf c' e1 e2 t ->
    le_term l (lepf_subst pf pfs) c e1[/s1/] e2[/s2/] t[/s2/]
    (*choosing s1 would be a strictly stronger conclusion.
      However, e2[/s2/] may not always have that type, so we must choose s2 *)
| le_term_by : forall l n c e1 e2 t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t ->
    wf_term l c e1 t ->
    wf_term l c e2 t ->
    is_nth_level l n ({< c |- e1 <# e2 .: t}) ->
    le_term l (lepf_by n) c e1 e2 t
| le_term_refl : forall l c e t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t ->
    wf_term l c e t ->
    le_term l lepf_refl c e e t
| le_term_trans : forall l pf1 pf2 c e1 e12 e2 t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t ->
    wf_term l c e1 t ->
    wf_term l c e2 t ->
    le_term l pf1 c e1 e12 t ->
    le_term l pf2 c e12 e2 t ->
    le_term l (lepf_trans pf1 pf2) c e1 e2 t
(* Conversion:

c |- e1 < e2 : t  ||
               /\ ||
c |- e1 < e2 : t' \/
*)
| le_term_conv : forall l pfs pft c e1 e2 t t',
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t' ->
    wf_term l c e1 t' ->
    wf_term l c e2 t' ->
    le_term l pft c e1 e2 t ->
    le_sort l pfs c t t' ->
    le_term l (lepf_conv pfs pft) c e1 e2 t'
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
with le_subst : lang -> seq lepf -> ctx -> subst -> subst -> ctx -> Prop :=
| le_subst_nil : forall l c,
    wf_lang l ->
    wf_ctx l c ->
    wf_ctx l [::] ->
    wf_subst l c [::] [::] ->
    le_subst l [::] c [::] [::] [::]
| le_subst_cons : forall l pf pfs c s1 s2 c' e1 e2 t,
    wf_lang l ->
    wf_ctx l c ->
    wf_ctx l (t::c') ->
    wf_subst l c (e1::s1) (t::c') ->
    wf_subst l c (e2::s2) (t::c') ->
    le_subst l pfs c s1 s2 c' ->
    le_term l pf c e1 e2 t[/s2/] ->
    (*choosing s1 would be a strictly stronger premise,
     but this suffices since t[/s1/] <# t[/s2/] *)
    le_subst l (pf::pfs) c (e1::s1) (e2::s2) (t::c')
with wf_ctx : lang -> ctx -> Prop :=
| wf_ctx_nil : forall l, wf_lang l -> wf_ctx l [::]
| wf_ctx_cons : forall l c v,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c v ->
    wf_ctx l (v::c)
(* TODO: add as auxilliary judgment
with le_ctx : lang -> ctx -> ctx -> Prop :=
| le_ctx_nil : forall l,
    wf_lang l ->
    wf_ctx l [::] ->
    le_ctx l [::] [::]
| le_ctx_cons : forall l c1 c2 v1 v2,
    wf_lang l ->
    wf_ctx l (v1::c1) ->
    wf_ctx l (v2::c2) ->
    le_sort l c2 c1 v2 v1 ->
    le_ctx l (v1::c1) (v2::c2) *)
with wf_rule : lang -> rule -> Prop :=
| wf_sort_rule : forall l c,
    wf_lang l ->
    wf_ctx l c ->
    wf_rule l ({| c |- sort})
| wf_term_rule : forall l c t,
    wf_lang l ->
    wf_ctx l c ->
    wf_sort l c t ->
    wf_rule l ({| c |- t})
| le_sort_rule : forall l c t1 t2,
    wf_lang l -> 
    wf_ctx l c ->
    wf_sort l c t1 ->
    wf_sort l c t2 ->
    wf_rule l ({< c |- t1 <# t2})
| le_term_rule : forall l c e1 e2 t,
    wf_lang l -> 
    wf_ctx l c ->
    wf_sort l c t ->
    wf_term l c e1 t ->
    wf_term l c e2 t ->
    wf_rule l ({< c |- e1 <# e2 .: t})
with wf_lang : lang -> Prop :=
| wf_lang_nil : wf_lang [::]
| wf_lang_cons : forall l r, wf_lang l -> wf_rule l r -> wf_lang (r::l).


(* TODOTODOTODOTODO: change hint dbs?*)
(* database of constructor hints. In general, this should be avoided 
   in favor of the databse below of related lemmas with fewer hypotheses *)
(*Create HintDb judgment_constructors discriminated.*)
Hint Constructors wf_sort le_sort
     wf_term le_term
     wf_subst le_subst
     wf_ctx wf_rule wf_lang : judgment_constructors.


(* build a database of presuppositions and judgment facts *)
(*Create HintDb judgment discriminated.*)

(* Presuppositions of language well-formedness *)
Lemma wf_sort_lang l c t : wf_sort l c t -> wf_lang l.
Proof using . by inversion. Qed.
Hint Immediate wf_sort_lang : judgment.

Lemma le_sort_lang l pf c t1 t2 : le_sort l pf c t1 t2 -> wf_lang l.
Proof using . by inversion. Qed.
Hint Immediate le_sort_lang : judgment.

Lemma wf_term_lang l c e t : wf_term l c e t -> wf_lang l.
Proof using . by inversion. Qed.
Hint Immediate wf_term_lang : judgment.

Lemma le_term_lang l pf c e1 e2 t
  : le_term l pf c e1 e2 t -> wf_lang l.
Proof using . by inversion. Qed.
Hint Immediate le_term_lang : judgment.

Lemma wf_subst_lang l c s c' : wf_subst l c s c' -> wf_lang l.
Proof using . by inversion. Qed.
Hint Immediate wf_subst_lang : judgment.

Lemma le_subst_lang l pf c s1 s2 c'
  : le_subst l pf c s1 s2 c' -> wf_lang l.
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

Lemma le_sort_ctx l pf c t1 t2
  : le_sort l pf c t1 t2 -> wf_ctx l c.
Proof using . by inversion. Qed.
Hint Immediate le_sort_ctx : judgment.

Lemma wf_term_ctx l c e t : wf_term l c e t -> wf_ctx l c.
Proof using . by inversion. Qed.
Hint Immediate wf_term_ctx : judgment.

Lemma le_term_ctx l pf c e1 e2 t
  : le_term l pf c e1 e2 t -> wf_ctx l c.
Proof using . by inversion. Qed.
Hint Immediate le_term_ctx : judgment.

Lemma wf_subst_ctx_in l c s c' : wf_subst l c s c' -> wf_ctx l c.
Proof using . by inversion. Qed.
Hint Immediate wf_subst_ctx_in : judgment.

Lemma wf_subst_ctx_out l c s c' : wf_subst l c s c' -> wf_ctx l c'.
Proof using . by inversion. Qed.
Hint Immediate wf_subst_ctx_out : judgment.

Lemma le_subst_ctx_in l pfs c s1 s2 c'
  : le_subst l pfs c s1 s2 c' -> wf_ctx l c.
Proof using . by inversion. Qed.
Hint Immediate le_subst_ctx_in : judgment.

Lemma le_subst_ctx_out l pfs c s1 s2 c'
  : le_subst l pfs c s1 s2 c' -> wf_ctx l c'.
Proof using . by inversion. Qed.
Hint Immediate le_subst_ctx_out : judgment.


(* Presuppositions of sort well-formedness *)
Lemma le_sort_sort_l l pf c t1 t2
  : le_sort l pf c t1 t2 -> wf_sort l c t1.
Proof using . by inversion. Qed.
Hint Immediate le_sort_sort_l : judgment.

Lemma le_sort_sort_r l pf c t1 t2
  : le_sort l pf c t1 t2 -> wf_sort l c t2.
Proof using . by inversion. Qed.
Hint Immediate le_sort_sort_r : judgment.

Lemma wf_term_sort l c e t : wf_term l c e t -> wf_sort l c t.
Proof using . by inversion. Qed.
Hint Immediate wf_term_sort : judgment.

Lemma le_term_sort l pf c e1 e2 t
  : le_term l pf c e1 e2 t -> wf_sort l c t.
Proof using . by inversion. Qed.
Hint Immediate le_term_sort : judgment.


(* Presuppositions of term well-formedness *)
Lemma le_term_term_l l pf c e1 e2 t
  : le_term l pf c e1 e2 t -> wf_term l c e1 t.
Proof using . inversion; try done. Qed.
Hint Immediate le_term_term_l : judgment.

Lemma le_term_term_r l pf c e1 e2 t
  : le_term l pf c e1 e2 t -> wf_term l c e2 t.
Proof using . by inversion. Qed.
Hint Immediate le_term_term_r : judgment.


(* Presuppositions of subst well-formedness *)
Lemma le_subst_subst_l l pf c s1 s2 c'
  : le_subst l pf c s1 s2 c' -> wf_subst l c s1 c'.
Proof using . by inversion. Qed.
Hint Immediate le_subst_subst_l : judgment.

Lemma le_subst_subst_r l pf c s1 s2 c'
  : le_subst l pf c s1 s2 c' -> wf_subst l c s2 c'.
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

(* TODO: move to exp, rule *)
Fixpoint erase e : Exp.exp :=
  match e with
  | var n => Exp.var n
  | con n s => Exp.con n (map erase s)
  | conv _ e => erase e
  end.

Definition erase_rule r : Rule.rule :=
  match r with
  | sort_rule c => Rule.sort_rule (map erase c)
  | term_rule c t => Rule.term_rule (map erase c) (erase t)
  | sort_le c t1 t2 => Rule.sort_le (map erase c) (erase t1) (erase t2)
  | term_le c e1 e2 t => Rule.term_le (map erase c) (erase e1) (erase e2) (erase t)
  end.

(*TODO: add this in the right place *)
Hint Resolve is_nth_level_in : judgment.


Lemma nth_error_map {A B : Type} (f : A -> B) l n e
  : List.nth_error l n = Some e -> List.nth_error (map f l) n = Some (f e).
Proof using .
  elim: n l; intros until l; case: l; simpl; try easy.
  intros a _; case => -> //.
Qed.
  
Lemma is_nth_level_erase l n r : is_nth_level l n r -> @is_nth_level Rule.rule_eqType (map erase_rule l) n (erase_rule r).
Proof using .
  unfold is_nth_level.
  rewrite size_map.
  move /andP => [nlt] /eqP.
  rewrite nlt; simpl.
  intros; apply /eqP.
  by apply: nth_error_map.
Qed.


Lemma is_nth_level_erase_var c n t : is_nth_level c n t -> @is_nth_level Exp.exp_eqType (map erase c) n (erase t).
Proof using .
  unfold is_nth_level.
  rewrite size_map.
  move /andP => [nlt] /eqP.
  rewrite nlt; simpl.
  intros; apply /eqP.
  by apply: nth_error_map.
Qed.


Lemma nth_level_fn {A B : Type} (f : A -> B) d l n : nth_level (f d) (map f l) n = f (nth_level d l n).
Proof using .
  unfold nth_level.
  rewrite size_map.
  case szn : (n < size l); auto.
  apply: nth_map.
  case: (size l) szn; try easy.
  intros; compute;
  apply sub_ord_proof.
Qed.          

Lemma erase_subst_comm e s : (erase e[/s/]) = Exp.exp_subst (map erase s) (erase e).
Proof.
  elim: e; simpl; auto.
  {
    intro n.
    unfold Exp.exp_subst.
    unfold exp_subst.
    simpl.
    unfold Exp.var_lookup; unfold var_lookup.
    change (Exp.var n) with (erase (var n)).
    symmetry.
    by apply: nth_level_fn.
  }
  {
    intro n; elim; simpl; auto.
    intros.
    inversion H0; subst.
    unfold Exp.exp_subst; simpl.
    f_equal.
    f_equal; eauto.
    pose p:= H H4.
    by case: p.
  }
Qed.

Lemma proof_impl_core
  : (forall (l : lang) pf c t1 t2,
        le_sort l pf c t1 t2 ->
        Core.le_sort (map erase_rule l) (map erase c) (erase t1) (erase t2))
    /\ (forall (l : lang) pfs c s1 s2 c',
           le_subst l pfs c s1 s2 c' ->
           Core.le_subst (map erase_rule l) (map erase c) (map erase s1) (map erase s2) (map erase c'))
    /\ (forall (l : lang) pf c e1 e2 t,
           le_term l pf c e1 e2 t ->
           Core.le_term (map erase_rule l) (map erase c) (erase e1) (erase e2) (erase t))
    /\ (forall (l : lang) c t,
           wf_sort l c t -> Core.wf_sort (map erase_rule l) (map erase c) (erase t))
    /\ (forall (l : lang) c s c',
           wf_subst l c s c' -> Core.wf_subst (map erase_rule l) (map erase c) (map erase s) (map erase c'))
    /\ (forall (l : lang) c e t,
           wf_term l c e t -> Core.wf_term (map erase_rule l) (map erase c) (erase e) (erase t))
    /\ (forall (l : lang) c,
           wf_ctx l c -> Core.wf_ctx (map erase_rule l) (map erase c))
    /\ (forall (l : lang) r,
           wf_rule l r -> Core.wf_rule (map erase_rule l) (erase_rule r))
    /\ (forall (l : lang),
           wf_lang l -> Core.wf_lang (map erase_rule l)).
Proof using .
  apply: ind; intros; rewrite ?erase_subst_comm; eauto with judgment.
  {
    constructor; eauto with judgment.
    apply: is_nth_level_in.
    change (Rule.sort_le (map erase c) (erase t1) (erase t2)) with (erase_rule (sort_le c t1 t2)).
    eapply is_nth_level_erase; eauto.
  }
  {
    simpl; constructor; eauto with judgment.
    rewrite -erase_subst_comm.
    done.    
  }
  {
    constructor; eauto with judgment.
    apply: is_nth_level_in.
    change (Rule.term_le (map erase c) (erase e1) (erase e2) (erase t)) with (erase_rule (term_le c e1 e2 t)).
    eapply is_nth_level_erase; eauto. 
  }
  {
    simpl; econstructor; eauto with judgment.
    change (Rule.sort_rule (map erase c')) with (erase_rule (sort_rule c')).
    eapply is_nth_level_erase; eauto. 
  }
  {
    simpl; econstructor; eauto with judgment.
    rewrite -erase_subst_comm.
    done.    
  }
  {
    simpl; econstructor; eauto with judgment.
    rewrite -erase_subst_comm.
    done.
    change (Rule.term_rule (map erase c') (erase t)) with (erase_rule (term_rule c' t)).
    eapply is_nth_level_erase; eauto.
  }
  {
    simpl.
    eapply Core.wf_term_var; eauto with judgment.
    eapply is_nth_level_erase_var; eauto.
  }
Qed.

Lemma in_ListIn : forall (A : eqType) (x : A) (l : seq A), x \in l -> List.In x l.
  intros until l; elim: l => //=.
  intros a l IH.
  rewrite in_cons; case /orP.
  - move /eqP ->; tauto.
  - move /IH; tauto.
Qed.    

Lemma in_is_nth_level {A : eqType} (a : A) (l : seq A) : a \in l -> exists n, is_nth_level l n a.
Proof.
  unfold is_nth_level.
  move /in_ListIn => lin.
  apply List.In_nth_error in lin.
  destruct lin.
  remember (size l - x.+1) as n.
  exists n.
  case nlt : (n < size l); simpl.
  suff: (x < size l).
  move => xlt.
  move: (sub_flip xlt Heqn).
  move <-; apply /eqP; auto.
  admit.
  admit.
Admitted.

Lemma core_impl_proof
  : (forall l c t1 t2,
        Core.le_sort l c t1 t2 ->
        exists lp pf cp t1p t2p, le_sort lp pf cp t1p t2p
                         /\ l = map erase_rule lp
                         /\ c = map erase cp
                         /\ t1 = erase t1p
                         /\ t2 = erase t2p)
    /\ (forall l c s1 s2 c',
           Core.le_subst l c s1 s2 c' ->
           exists lp pfs cp s1p s2p c'p, le_subst lp pfs cp s1p s2p c'p
                         /\ l = map erase_rule lp
                         /\ c = map erase cp
                         /\ s1 = map erase s1p
                         /\ s2 = map erase s2p
                         /\ c' = map erase c'p)
    /\ (forall l c e1 e2 t,
           Core.le_term l c e1 e2 t ->
           exists lp pf cp e1p e2p tp, le_term lp pf cp e1p e2p tp
                         /\ l = map erase_rule lp
                         /\ c = map erase cp
                         /\ e1 = erase e1p
                         /\ e2 = erase e2p
                         /\ t = erase tp)
    /\ (forall l c t,
           Core.wf_sort l c t ->
           exists lp cp tp, wf_sort lp cp tp
                         /\ l = map erase_rule lp
                         /\ c = map erase cp
                         /\ t = erase tp)
    /\ (forall l c s c',
           Core.wf_subst l c s c' ->
           exists lp cp sp c'p, wf_subst lp cp sp c'p
                         /\ l = map erase_rule lp
                         /\ c = map erase cp
                         /\ s = map erase sp
                         /\ c' = map erase c'p)
    /\ (forall l c e t,
           Core.wf_term l c e t ->
           exists lp cp ep tp, wf_term lp cp ep tp
                         /\ l = map erase_rule lp
                         /\ c = map erase cp
                         /\ e = erase ep
                         /\ t = erase tp)
    /\ (forall l c,
           Core.wf_ctx l c ->
           exists lp cp, wf_ctx lp cp
                         /\ l = map erase_rule lp
                         /\ c = map erase cp)
    /\ (forall l r,
           Core.wf_rule l r ->
           exists lp rp, wf_rule lp rp
                         /\ l = map erase_rule lp
                         /\ r = erase_rule rp)
    /\ (forall (l : Rule.lang),
           Core.wf_lang l ->
           exists lp, wf_lang lp /\ l = map erase_rule lp).
Proof using .

Scheme Cle_sort_ind' := Minimality for Core.le_sort Sort Prop
  with Cle_subst_ind' := Minimality for Core.le_subst Sort Prop
  with Cle_term_ind' := Minimality for Core.le_term Sort Prop
  with Cwf_sort_ind' := Minimality for Core.wf_sort Sort Prop
  with Cwf_subst_ind' := Minimality for Core.wf_subst Sort Prop
  with Cwf_term_ind' := Minimality for Core.wf_term Sort Prop
  with Cwf_ctx_ind' := Minimality for Core.wf_ctx Sort Prop
  with Cwf_rule_ind' := Minimality for Core.wf_rule Sort Prop
  with Cwf_lang_ind' := Minimality for Core.wf_lang Sort Prop.

Combined Scheme Cind from
         Cle_sort_ind',
         Cle_subst_ind',
         Cle_term_ind',
         Cwf_sort_ind',
         Cwf_subst_ind',
         Cwf_term_ind',
         Cwf_ctx_ind',
         Cwf_rule_ind',
         Cwf_lang_ind'.
apply: Cind.
{
  intros.
  repeat match goal with
         | H : exists _, _ |- _ => destruct H
         | H : _ /\ _ |- _ => destruct H
         end.
  match goal with
  | H : is_true(_ \in _) |- _ => apply in_is_nth_level in H; destruct H
  end.
  repeat esplit; eauto with judgment.
  apply: le_sort_by; eauto with judgment.
  2:{
    instantiate (1:=x8).
    subst.
    is_nth_level_erase.
    

    
  TODO: need that related proof terms are interchangeable?

  Fail.

Lemma mono_rule l r r' : wf_rule l r -> wf_rule l r' -> wf_rule (r::l) r'.
Proof using .
  move => wfr.
  inversion; constructor; try by constructor; auto.
  all: try by eapply mono; eauto.
Qed.

Lemma wf_lang_prefix l1 l2 : wf_lang (l1 ++ l2) -> wf_lang l2.
Proof using .
  elim: l1; auto.
  move => r l1 IH.
  rewrite cat_cons => wfl.
  inversion wfl.
  eauto.
Qed.

Lemma wf_lang_rst : forall l a, wf_lang (a :: l) -> wf_lang l.
Proof using .
  intro_to wf_lang; inversion; eauto.
Qed.

Lemma rule_in_wf l r : wf_lang l -> r \in l -> wf_rule l r.
Proof using .
 elim; first by compute.
 intro_to is_true.
 rewrite in_cons; case /orP; first move /eqP ->; eauto using mono_rule.
Qed.
Hint Resolve rule_in_wf : judgment.


(* ==============================
   Context relation transitivity
   ============================= *)

(* TODO: move to utils*)
Lemma nth_level_size_lt {A:eqType} l n e : @is_nth_level A l n e -> n < size l.
Proof using .
  unfold is_nth_level.
  move /andP; tauto.
Qed.

Lemma wf_subst_len_eq l c s c' : wf_subst l c s c' -> size s = size c'.
Proof using .
  elim: s c'.
  - case; simpl; auto; intro_to wf_subst; by inversion.
  - intros until c'; elim: c'.
    + simpl; auto; intro_to wf_subst; by inversion.
    + simpl; intros; f_equal;
      specialize H with l1; destruct H;
      inversion H1;
      eauto with judgment.
Qed.

(* manual induction scheme *)
Lemma nat2_mut_ind (Pl Pr : nat -> Prop)
  : Pl 0 ->
    Pr 0 ->
    (forall n, Pl n -> Pr n -> Pr (n.+1)) ->
    (forall n, Pl n -> Pr n -> Pl (n.+1)) ->
    (forall n, Pl n /\ Pr n).
Proof using .
  move => Pl0 Pr0 Plr Prl.
  elim; auto.
  move => n; case => Pln Prn; split; auto.
Qed.

Scheme ctx_refl_ind := Minimality for wf_ctx Sort Prop.


Scheme wf_sort_subst_props_ind := Minimality for wf_sort Sort Prop
  with wf_subst_subst_props_ind := Minimality for wf_subst Sort Prop
  with wf_term_subst_props_ind := Minimality for wf_term Sort Prop.

Combined Scheme subst_props_ind from
         wf_sort_subst_props_ind,
wf_subst_subst_props_ind,
wf_term_subst_props_ind.
(*TODO: will eventually want a library of betterinduction schemes for same reason I wantedparameters*)

      
Lemma wf_is_ws : (forall l c t, wf_sort l c t -> ws_exp (size c) t)
                 /\ (forall l c s c', wf_subst l c s c' -> ws_subst (size c) s)
                 /\ (forall l c e t, wf_term l c e t -> ws_exp (size c) e).
Proof using .
  apply: subst_props_ind; simpl; intros; try apply /andP; auto; try apply: nth_level_size_lt; eauto.
Qed.
Definition wf_is_ws_sort := proj1 wf_is_ws.
Hint Resolve wf_is_ws_sort : judgment.

Definition wf_is_ws_subst := proj1 (proj2 wf_is_ws).
Hint Resolve wf_is_ws_subst : judgment.

Definition wf_is_ws_term := proj2 (proj2 wf_is_ws).
Hint Resolve wf_is_ws_term : judgment.
(*
Lemma wf_subst_conv l c s c' c'' : le_ctx l c' c'' -> wf_subst l c s c' -> wf_subst l c s c''.
Proof.
  elim: c' s c''; intros until s; case: s; intros until c''; case: c'';
      try solve [ eauto with judgment judgment_constructors
                | intro_to le_ctx; inversion
                | intro_to wf_subst; inversion].
  intro_to le_ctx; inversion; inversion; subst.
  suff: wf_subst l c l1 l2; [move => wfs | by apply: H; eauto with judgment].
  econstructor; try by eauto with judgment.
  suff: le_sort l c c a[/l1/] a1[/l1/].
  eauto with judgment_constructors judgment.
  eapply le_sort_subst; 
    eauto with judgment_constructors judgment.
  by apply: le_ctx_refl.
  inversion H8; subst.
  suff: le_subst l c c l1 l1 
  2:{
    
    need to go from a < a1 to a[/l1/] < ...
  econstructor; auto.
  auto with judgment judgment_constructors.
  TODO: is this true?

  
Lemma le_sort_subst l c1 c2 t1 t2 : wf_subst c s c1 -> le_sort l c1 c2 t1 t2 -> le_sort l c c t1[/l1/] t2[/l1/].


TODO: do I need to mix in something about relatedness below?
 *)

Lemma wf_ctx_suffix l c' c : wf_ctx l (c' ++ c) -> wf_ctx l c.
Proof using .
  elim: c'; auto; simpl.
  intro_to wf_ctx; inversion; eauto.
Qed.
Hint Immediate wf_ctx_suffix : judgment.

(*
Lemma wf_subst_conv l c1 s c2 : wf_subst l c1 s c2 -> forall c2', le_ctx l c2' c2 -> wf_subst l c1 s c2'.
Proof.
  elim; eauto with judgment; intros until c2'; inversion.
  eauto with judgment judgment_constructors.
  constructor; eauto with judgment.
  subst.
  eapply wf_term_conv; eauto with judgment.
  TODO: needs to be in the mutualbelow?*)

Lemma le_subst_refl l c s c' : wf_subst l c s c' -> le_subst l c s s c'.
Proof using .
  elim; econstructor; eauto with judgment judgment_constructors.
Qed.



Scheme le_sort_mono_ctx_ind := Minimality for le_sort Sort Prop
  with le_subst_mono_ctx_ind := Minimality for le_subst Sort Prop
  with le_term_mono_ctx_ind := Minimality for le_term Sort Prop
  with wf_sort_mono_ctx_ind := Minimality for wf_sort Sort Prop
  with wf_subst_mono_ctx_ind := Minimality for wf_subst Sort Prop
  with wf_term_mono_ctx_ind := Minimality for wf_term Sort Prop.

Combined Scheme mono_ctx_ind from
         le_sort_mono_ctx_ind,
         le_subst_mono_ctx_ind,
         le_term_mono_ctx_ind,
         wf_sort_mono_ctx_ind,
         wf_subst_mono_ctx_ind,
         wf_term_mono_ctx_ind.

(*
Lemma wf_id_subst l c c' :  wf_ctx l (c'++c) -> wf_subst l (c' ++ c) (id_subst (size c)) c.
Proof with eauto with judgment judgment_constructors.
  elim: c c'; simpl...
  intros; constructor...
  move: H0; rewrite -!cat_rcons; by eauto.
  apply wf_ctx_suffix in H0; by inversion H0.
  rewrite id_subst_identity id_subst_size.
  constructor...
  {
    elim: c' H0; simpl.
    - inversion.
  
  idtac...
  Search _ id_subst.
  Search _ (wf_ctx _ (_++_)).
  *)

Lemma is_nth_level_cat {A : eqType} l (a : A) l' : is_nth_level (l ++ a :: l') (size l') a.
Proof using .
  unfold is_nth_level.
  apply /andP; split;
  rewrite size_cat; simpl.
  apply: ltn_addl; auto.
  rewrite addnC; rewrite add_sub.
  elim: l; simpl; auto.
Qed.

(* manual induction scheme *)
Lemma nat3_mut_ind' (Pl Pr1 Pr2 : nat -> Prop)
  : Pl 0 ->
    Pr1 0 ->
    Pr2 0 ->
    (forall n, Pl n -> Pr1 n -> Pr1 (n.+1)) ->
    (forall n, Pl n -> Pr1 n -> Pr2 n -> Pr2 n.+1) ->
    (forall n, Pr1 n -> Pr2 n -> Pl n) ->
    (forall n, Pl n /\ Pr1 n /\ Pr2 n).
Proof using .
  move => Pl0 Pr10 Pr20 Plr1 Plr2 Prl.
  elim; auto.
  move => n; case => Pln Prn; split; eauto.
  apply: Prl.
  apply: Plr1; auto.
  tauto.
  apply: Plr2; auto.
  tauto.
  tauto.
  split.
  apply: Plr1; auto; tauto.
  apply: Plr2; auto.
  tauto.
  tauto.
Qed.

(* TODO: move to utils *)
Ltac rewrite_matching lem c :=
      match goal with [ H : context[c] |- _] =>
                      rewrite lem in H end.


Lemma is_nth_level_suffix {A : eqType} c' c n (t : A) : is_nth_level c n t -> is_nth_level (c'++c) n t.
Proof using .
  elim: c'; simpl; auto using is_nth_level_cons.
Qed.

Lemma mono_ctx'
  : forall n, ((forall (l : lang) c t1 t2,
                              le_sort l c t1 t2 ->
                              n >= (size c).+1 ->
                              forall c', wf_ctx l (c' ++ c) -> le_sort l (c' ++ c) t1 t2)
                          /\ (forall (l : lang) c s1 s2 c',
                                 le_subst l c s1 s2 c' ->
                                 n >= (size c).+1 ->
                                 forall c'', wf_ctx l (c'' ++ c) -> le_subst l  (c'' ++ c) s1 s2 c')
                          /\ (forall (l : lang) c e1 e2 t,
                                 le_term l c e1 e2 t ->
                                 n >= (size c).+1 ->
                                 forall c', wf_ctx l (c' ++ c) ->
                                 le_term l (c' ++ c) e1 e2 t)
                          /\ (forall (l : lang) c t,
                                 wf_sort l c t -> 
                                 n >= (size c).+1 ->
                                 forall c', wf_ctx l (c' ++ c) -> wf_sort l (c' ++ c) t)
                          /\ (forall (l : lang) c s c',
                                 wf_subst l c s c' ->
                                 n >= (size c).+1 -> 
                                 forall c'', wf_ctx l (c'' ++ c) ->
                                             wf_subst l (c'' ++ c) s c')
                          /\ (forall (l : lang) c e t,
                                 wf_term l c e t -> 
                                 n >= (size c).+1 ->
                     forall c', wf_ctx l (c' ++ c) ->
                                wf_term l (c' ++ c) e t))
              /\ (forall l c c', n >= (size c).+1 -> wf_ctx l (c'++c) -> wf_subst l (c' ++ c) (id_subst (size c)) c)
              /\ (forall l c c', n >= (size c).+1 -> wf_ctx l (c'++c) ->
                                 le_subst l (c' ++ c) (id_subst (size c)) (id_subst (size c)) c).
Proof with eauto with judgment using .
  eapply nat3_mut_ind'; simpl; try easy.
  {
    intros until c; elim: c; simpl; intros until c'.
    all: repeat match goal with [ H : _ /\ _ |- _] => destruct H end.
    rewrite !cats0; constructor; by eauto with judgment judgment_constructors.
    rewrite !id_subst_size.
    constructor; eauto with judgment.
    all: match goal with [ H : context[wf_ctx] |- _] => move: H end.
    rewrite -!cat_rcons; by eauto.
    move /wf_ctx_suffix; by inversion.
    rewrite id_subst_identity.
    constructor; eauto with judgment.
    rewrite -cat_rcons.
    match goal with
      H : context[ _ -> wf_sort _ _ _] |- _ => apply: H
    end; eauto with judgment.
    match goal with [ H : context[wf_ctx] |- _] => move: H end.
    move /wf_ctx_suffix; by inversion.
    by rewrite cat_rcons.
    by apply is_nth_level_cat.
  }
  {
    intros until c; elim: c; simpl; intros until c'.
    all: repeat match goal with [ H : _ /\ _ |- _] => destruct H end.
    rewrite !cats0; constructor; by eauto with judgment judgment_constructors.
    rewrite !id_subst_size.
    constructor; eauto with judgment.
    all: match goal with [ H : context[wf_ctx] |- _] => move: H end.
    { (*TODO: streamline; currently copied *)
      constructor; eauto with judgment.
      all: match goal with [ H : context[wf_ctx] |- _] => move: H end.
      rewrite -!cat_rcons; by eauto.
      move /wf_ctx_suffix; by inversion.
      rewrite id_subst_identity.
      constructor; eauto with judgment.
      rewrite -cat_rcons.
      match goal with
        H : context[ _ -> wf_sort _ _ _] |- _ => apply: H
      end; eauto with judgment.
      match goal with [ H : context[wf_ctx] |- _] => move: H end.
      move /wf_ctx_suffix; by inversion.
        by rewrite cat_rcons.
          by apply is_nth_level_cat.
    }
    
    { (*TODO: streamline; currently copied *)
      constructor; eauto with judgment.
      all: match goal with [ H : context[wf_ctx] |- _] => move: H end.
      rewrite -!cat_rcons; by eauto.
      move /wf_ctx_suffix; by inversion.
      rewrite id_subst_identity.
      constructor; eauto with judgment.
      rewrite -cat_rcons.
      match goal with
        H : context[ _ -> wf_sort _ _ _] |- _ => apply: H
      end; eauto with judgment.
      match goal with [ H : context[wf_ctx] |- _] => move: H end.
      move /wf_ctx_suffix; by inversion.
        by rewrite cat_rcons.
          by apply is_nth_level_cat.
    }
    all: match goal with [ H : context[wf_ctx] |- _] => move: H end.
    rewrite -!cat_rcons; by eauto.
    rewrite id_subst_identity.
    intros; eapply le_term_refl; eauto with judgment.
    rewrite -cat_rcons.
    match goal with
      H : context[ _ -> wf_sort _ _ _] |- _ => apply: H
    end; eauto with judgment.
    match goal with [ H : context[wf_ctx] |- _] => move: H end.
    move /wf_ctx_suffix; by inversion.
      by rewrite cat_rcons.
      constructor; eauto with judgment.
      rewrite -cat_rcons.
      match goal with
        H : context[ _ -> wf_sort _ _ _] |- _ => apply: H
      end; eauto with judgment.
      match goal with [ H : context[wf_ctx] |- _] => move: H end.
      move /wf_ctx_suffix; by inversion.
        by rewrite cat_rcons.
          by apply is_nth_level_cat.
  }
  intros.
  apply: mono_ctx_ind; intros.
  all: try by econstructor; eauto with judgment.
  {
    rewrite <-(@id_subst_identity t1 (size c)).
    rewrite <-(@id_subst_identity t2 (size c)).
    apply: le_sort_subst; eauto with judgment.
    all: rewrite ?id_subst_identity ?id_subst_size; eauto with judgment judgment_constructors.
  }
  {
    rewrite <-(@id_subst_identity t1'[/s1/] (size c)).
    rewrite <-(@id_subst_identity t2'[/s2/] (size c)).
    apply: le_sort_subst; eauto with judgment.
    all: rewrite ?id_subst_identity ?id_subst_size; eauto with judgment.
    eapply le_sort_subst; eauto with judgment.
  }
  {
    rewrite <-(@id_subst_identity t (size c)).
    apply: le_sort_subst; eauto with judgment.
    all: rewrite ?id_subst_identity ?id_subst_size; eauto with judgment.
    eapply le_sort_refl; eauto with judgment.
  }
  {
    apply: le_sort_trans; eauto with judgment.
  }
  {
    rewrite <-(@id_subst_identity e1 (size c)).
    rewrite <-(@id_subst_identity e2 (size c)).
    rewrite <-(@id_subst_identity t (size c)).
    apply: le_term_subst; eauto with judgment.
    all: rewrite ?id_subst_identity ?id_subst_size; eauto with judgment.
    eapply le_term_by; eauto with judgment.
  }
  by eauto with judgment judgment_constructors.
  by apply: le_term_trans; eauto with judgment.
  by apply: le_term_conv; eauto with judgment.
  {
    constructor; eauto with judgment.
    by apply: is_nth_level_suffix.
  }
Qed.

Lemma mono_ctx
  : (forall (l : lang) c t1 t2,
        le_sort l c t1 t2 ->
        forall c', wf_ctx l (c' ++ c) -> le_sort l (c' ++ c) t1 t2)
    /\ (forall (l : lang) c s1 s2 c',
           le_subst l c s1 s2 c' ->
           forall c'', wf_ctx l (c'' ++ c) -> le_subst l  (c'' ++ c) s1 s2 c')
    /\ (forall (l : lang) c e1 e2 t,
           le_term l c e1 e2 t ->
           forall c', wf_ctx l (c' ++ c) ->
                      le_term l (c' ++ c) e1 e2 t)
    /\ (forall (l : lang) c t,
           wf_sort l c t ->
           forall c', wf_ctx l (c' ++ c) -> wf_sort l (c' ++ c) t)
    /\ (forall (l : lang) c s c',
           wf_subst l c s c' ->
           forall c'', wf_ctx l (c'' ++ c) ->
                       wf_subst l (c'' ++ c) s c')
    /\ (forall (l : lang) c e t,
           wf_term l c e t ->
           forall c', wf_ctx l (c' ++ c) ->
                      wf_term l (c' ++ c) e t).
Proof using .
  repeat split; intros; eapply mono_ctx'; eauto.
Qed.

Lemma wf_id_subst l c : wf_ctx l c -> wf_subst l c (id_subst (size c)) c. 
Proof using .
  change c with ([::] ++ c) at 1.
  eapply mono_ctx'; eauto.
Qed.


Scheme wf_sort_mono_subst_ind := Minimality for wf_sort Sort Prop
  with wf_subst_mono_subst_ind := Minimality for wf_subst Sort Prop
  with wf_term_mono_subst_ind := Minimality for wf_term Sort Prop.

Combined Scheme mono_subst_ind from
wf_sort_mono_subst_ind,
wf_subst_mono_subst_ind,
wf_term_mono_subst_ind.


Lemma subst_nil e : e [/[::]/] = e.
Proof using .
  elim: e; auto.
  unfold exp_subst; intros; simpl.
  f_equal.
  elim: l H; simpl; auto.
  intros.
  f_equal; tauto.
Qed.

Lemma subst_strengthen s' s e : ws_exp (size s) e -> e[/s'++s/] = e[/s/].
Proof using .
  elim: e.
  {
    unfold exp_subst; simpl; intros.
    unfold var_lookup.
    unfold nth_level.
    rewrite size_cat H.
    suff: n < size s' + size s => [->|].
    rewrite nth_cat.
    rewrite -addnBA; auto.
    rewrite -ltn_subRL.
    rewrite sub_n_n; simpl.
    by rewrite add_sub.
    by apply ltn_addl.
  }
  {
    intro n; elim; auto.
    unfold exp_subst; simpl.
    intro_to and; case.
    intro_to is_true; case /andP.
    intros; f_equal; f_equal; auto.
    move: (H b b0); case; auto.
  }
Qed.
 
Lemma wf_subst_drop n l c' s c : wf_subst l c' s c -> wf_subst l c' (drop n s) (drop n c).
Proof using .
  elim: n s c; first intros; rewrite ?drop0; auto.
  intros until s; case: s; intros until c; case: c; intro_to wf_subst; inversion; simpl; eauto with judgment.
Qed.
  
Lemma wf_nth l c' s c a b n : n < size c -> wf_subst l c' s c -> wf_term l c' (nth a s n) (nth b c n) [/s/].
Proof using .
  intros.
  erewrite <-(@cat_take_drop n _ s).
  erewrite <-(@cat_take_drop n _ c).
  rewrite !nth_cat.
  suff: n < size s; [ intro nlts | erewrite wf_subst_len_eq; eauto].
  rewrite !size_takel; auto.
  rewrite !ltnn.
  rewrite !sub_n_n !nth0.
  move: H0 => /(@wf_subst_drop n).
  generalize (take n s) as s'.
  elim: n c s H nlts; intros until c; case: c; try easy; intros until s; case: s; try easy.
  {
    intros e s t c; simpl.
    intro_to wf_subst; inversion; subst.
    rewrite -cat_rcons.
    rewrite subst_strengthen; auto.
    erewrite wf_subst_len_eq; eauto with judgment.
  }
  {
    intros.
    simpl.
    eauto with judgment.
  }
Qed.


Lemma ws_exp_mono sz e : ws_exp sz e -> ws_exp sz.+1 e.
Proof using .
  elim: e; simpl; auto.
  intros until l; elim: l; simpl; auto.
  intro_to and; case.
  intro_to is_true; move /andP; case.
  intros; apply /andP; split.
  exact (a0 a1).
  apply: H; auto.
Qed.
  
Lemma ws_ctx_nth l c a n : n < size c -> wf_ctx l c -> ws_exp (size c) (nth a c n).
Proof using .
  elim: n c; intros until c; case: c; try easy.
  all: intro_to wf_ctx; inversion; simpl.
  all: apply: ws_exp_mono; eauto with judgment.
Qed.

Lemma mono_subst
  : (forall (l : lang) c t1 t2,
        le_sort l c t1 t2 ->
        forall c' s1 s2, le_subst l c' s1 s2 c ->
                         le_sort l c' t1[/s1/] t2[/s2/])
    /\ (forall (l : lang) c s1 s2 c',
           le_subst l c s1 s2 c' ->
           forall c'' s1' s2', le_subst l c'' s1' s2' c ->
                               le_subst l c'' (subst_cmp s1 s1') (subst_cmp s2 s2') c')
    /\ (forall (l : lang) c t,
           wf_sort l c t -> 
           forall c' s, wf_subst l c' s c ->
                        wf_sort l c' t[/s/])
    /\ (forall (l : lang) c s c',
           wf_subst l c s c' -> 
           forall c'' s', wf_subst l c'' s' c ->
                          wf_subst l c'' (subst_cmp s s') c')
    /\ (forall (l : lang) c e t,
           wf_term l c e t -> 
           forall c' s, wf_subst l c' s c ->
                        wf_term l c' e[/s/] t[/s/]).
Proof with eauto with judgment judgment_constructors using .

Scheme le_sort_mono_subst_ind' := Minimality for le_sort Sort Prop
  with le_subst_mono_subst_ind' := Minimality for le_subst Sort Prop
  with wf_sort_mono_subst_ind' := Minimality for wf_sort Sort Prop
  with wf_subst_mono_subst_ind' := Minimality for wf_subst Sort Prop
  with wf_term_mono_subst_ind' := Minimality for wf_term Sort Prop.

Combined Scheme mono_subst_ind' from
         le_sort_mono_subst_ind',
         le_subst_mono_subst_ind',
         wf_sort_mono_subst_ind',
         wf_subst_mono_subst_ind',
         wf_term_mono_subst_ind'.
  apply: mono_subst_ind';intros; simpl.
  all:idtac...
  {
    constructor...
    suff: (ws_exp (size s2) t).
    intro.
    rewrite !sep_subst_cmp; auto.
    move: (H3 c'' s1' (le_subst_subst_l H9)); inversion; subst.
    move: (H5 c'' s2' (le_subst_subst_r H9)); inversion; subst.
    apply: le_term_subst...
    all: rewrite -?sep_subst_cmp; auto.
    idtac...
    apply: wf_term_conv; eauto with judgment.
    apply: le_sort_subst...
    erewrite wf_subst_len_eq; eauto with judgment.
    inversion H1...
  }
  unfold exp_subst; simpl...
  {
    constructor...
    rewrite !sep_subst_cmp; try erewrite wf_subst_len_eq...
  }
   {
    suff: ws_exp (size s) t;[intro|].
    rewrite con_subst_cmp -sep_subst_cmp...
    apply: wf_term_by...
    rewrite sep_subst_cmp...
    erewrite wf_subst_len_eq; eauto.
    apply is_nth_level_in in H3.
    apply rule_in_wf in H3...
    inversion H3...
  }
  {
    apply: wf_term_conv...
    apply: H6.
    apply: le_subst_refl... (*TODO: add to hints*)
  }
  {
    unfold exp_subst at 1; simpl.
    (*TODO: should this be a separate lemma?*)
    unfold var_lookup.
    suff: n < size c;
      [intro nltc | eauto; move: H3 => /andP; tauto].
    suff: n<size s; [intro nlts | erewrite wf_subst_len_eq; eauto].
    erewrite fn_to_is_nth_level in H3; eauto.
    move: H3 H2 => /eqP <-.
    intros.
    unfold nth_level; rewrite nlts nltc; simpl.
    erewrite wf_subst_len_eq; eauto.
    remember (size c - n.+1) as m.
    suff: m < size c.
    2:{
      rewrite Heqm.
      rewrite ltn_subLR ?addSnnS; auto.
      by apply ltn_addl.
    }
    intro mltc.
    suff: m < size s;[intro mtls | erewrite wf_subst_len_eq; eauto].
    clear Heqm nltc nlts; elim: m mltc mtls.    
    case: c H0 H1 H4 H2; first easy; case: s; first easy; intros.
    simpl.
    inversion H4; subst.
    change (a::l0) with ([::a]++l0).
    rewrite subst_strengthen; eauto with judgment.
    erewrite wf_subst_len_eq; eauto with judgment.

    case: c H0 H1 H4 H2; case: s; simpl; try easy; intros.
    change (a::l0) with ([::a]++l0).
    rewrite subst_strengthen; eauto with judgment.
    apply: wf_nth; eauto with judgment.
    by inversion H4.
    inversion H4; subst.
    erewrite wf_subst_len_eq; eauto with judgment.
    instantiate (1:=var n).
    apply: ws_ctx_nth; eauto.
    inversion H13; eauto.
  }
Qed.


(*TODO: how many to add to hint db?*)
Definition le_subst_on_sort := proj1 mono_subst.
Hint Resolve le_subst_on_sort : judgment.

Definition le_subst_on_subst := proj1 (proj2 mono_subst).
Hint Resolve le_subst_on_subst : judgment.
 
Definition wf_subst_on_sort := proj1 (proj2 (proj2 mono_subst)).
Hint Resolve wf_subst_on_sort : judgment.
 
Definition wf_subst_on_subst := proj1 (proj2 (proj2 (proj2 mono_subst))).
Hint Resolve wf_subst_on_subst : judgment.

Definition wf_subst_on_term  := proj2 (proj2 (proj2 (proj2 mono_subst))).
Hint Resolve wf_subst_on_term : judgment.

    
(* minimal constructors *)
(* we add these as hints rather than the actual constructors
   since they require fewer hypotheses *)

Lemma wf_sort_by' : forall l c n s c',
    is_nth_level l n (sort_rule c') ->
    wf_subst l c s c' ->
    wf_sort l c (con n s).
Proof using .
   eauto with judgment judgment_constructors.
Qed.
Hint Resolve wf_sort_by' : judgment.

Lemma le_sort_by' : forall l c t1 t2,
    wf_lang l ->
    ({< c |- t1 <# t2}) \in l ->
    le_sort l c t1 t2.
Proof using .
  intros.
  pose rwf := rule_in_wf H H0; inversion rwf.
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve le_sort_by' : judgment.

Lemma le_sort_subst' : forall l c s1 s2 c' t1 t2,
    le_subst l c s1 s2 c' ->
    le_sort l c' t1 t2 ->
    le_sort l c t1[/s1/] t2[/s2/].
Proof using .
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve le_sort_subst' : judgment.

Lemma le_sort_refl' : forall l c t,
    wf_sort l c t ->
    le_sort l c t t.
Proof using .
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve le_sort_refl' : judgment.
  
Lemma le_sort_trans' : forall l c t1 t12 t2,
    le_sort l c t1 t12 ->
    le_sort l c t12 t2 ->
    le_sort l c t1 t2.
Proof using .
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve le_sort_trans' : judgment.

Lemma wf_term_by' : forall l c n s c' t,
    is_nth_level l n ({| c' |- t}) ->
    wf_subst l c s c' ->
    wf_term l c (con n s) t[/s/].
Proof with (eauto with judgment judgment_constructors) using .
  intros.
  suff: wf_lang l...
  intro H1.
  suff: ({|c' |- t}) \in l.
  intro H2.
  pose rwf := rule_in_wf H1 H2.
  econstructor...
  apply: wf_subst_on_sort...
  by inversion rwf.
  eapply is_nth_level_in; eauto.
Qed.
Hint Resolve wf_term_by' : judgment.

Lemma wf_term_conv' : forall l c e t t',
    wf_term l c e t ->
    le_sort l c t t' ->
    wf_term l c e t'.
Proof using .
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve wf_term_conv' : judgment.

(* TODO:put somewhere better*)
Lemma wf_ctx_in l c t : wf_ctx l c -> t \in c -> wf_sort l c t.
Proof using .
  elim: c; simpl; intro_to is_true; try by compute.
  rewrite in_cons.
  inversion H0; subst.
  move /orP; case.
  move /eqP ->.
  all: intros; change (a::l0) with ([::a]++l0);
  eapply mono_ctx;
  eauto with judgment.
Qed.

Lemma wf_term_var' : forall l c n t,
    wf_ctx l c ->
    is_nth_level c n t ->
    wf_term l c (var n) t.
Proof with (eauto with judgment) using .
  intros.
  suff: wf_sort l c t; eauto using wf_term_var with judgment.
  suff: t \in c; eauto using is_nth_level_in.
  eauto using wf_ctx_in.
Qed.
Hint Resolve wf_term_var' : judgment.

Lemma le_term_by' : forall l c e1 e2 t,
    wf_lang l ->
    ({< c |- e1 <# e2 .: t}) \in l ->
    le_term l c e1 e2 t.
Proof using .
  intros.
  move: (rule_in_wf H H0).
  inversion;
  eauto using le_term_by with judgment.
Qed.
Hint Resolve le_term_by' : judgment.

Lemma le_term_subst' : forall l c s1 s2 c' e1 e2 t,
    le_subst l c s1 s2 c' ->
    le_term l c' e1 e2 t ->
    le_term l c e1[/s1/] e2[/s2/] t[/s2/].
Proof using.
  intros; apply: le_term_subst; eauto with judgment.
Qed.
Hint Resolve le_term_subst' : judgment.

Lemma le_term_refl' : forall l c e t,
    wf_term l c e t ->
    le_term l c e e t.
Proof using.
  intros; apply: le_term_refl; eauto with judgment.
Qed.
Hint Resolve le_term_refl' : judgment.
  
Lemma le_term_trans' : forall l c e1 e12 e2 t,
    le_term l c e1 e12 t ->
    le_term l c e12 e2 t ->
    le_term l c e1 e2 t.
Proof using.
  intros; apply: le_term_trans; eauto with judgment.
Qed.
Hint Resolve le_term_trans' : judgment.

Lemma le_term_conv' : forall l c e1 e2 t t',
    le_term l c e1 e2 t ->
    le_sort l c t t' ->
    le_term l c e1 e2 t'.
Proof using.
  intros; apply: le_term_conv; eauto with judgment.
Qed.
Hint Resolve le_term_conv' : judgment.

Lemma wf_subst_nil' : forall l c,
    wf_ctx l c ->
    wf_subst l c [::] [::].
Proof using.
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve wf_subst_nil' : judgment.

Lemma wf_subst_cons' : forall l c s c' e t,
    wf_subst l c s c' ->
    wf_sort l c' t ->
    wf_term l c e t[/s/] ->
    wf_subst l c (e::s) (t::c').
Proof using.
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve wf_subst_cons' : judgment.

Lemma le_subst_nil' : forall l c,
    wf_ctx l c ->
    le_subst l c [::] [::] [::].
Proof using.
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve le_subst_nil' : judgment.

Lemma le_subst_cons' : forall l c s1 s2 c' e1 e2 t,
    wf_subst l c (e1::s1) (t::c') -> (*TODO: can we reduce the assumptions?*)
    le_subst l c s1 s2 c' ->
    le_term l c e1 e2 t[/s2/] ->
    (*choosing s1 would be a strictly stronger premise,
     but this suffices since t[/s1/] <# t[/s2/] *)
    le_subst l c (e1::s1) (e2::s2) (t::c').
Proof using.
  intros; apply: le_subst_cons; eauto with judgment judgment_constructors.
  inversion H; eauto with judgment.
Qed.
Hint Resolve le_subst_cons' : judgment.

Hint Resolve wf_ctx_nil : judgment.

Lemma wf_ctx_cons' : forall l c v,
    wf_sort l c v ->
    wf_ctx l (v::c).
Proof using.
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve wf_ctx_cons' : judgment.

Lemma wf_sort_rule' : forall l c,
    wf_ctx l c ->
    wf_rule l ({| c |- sort}).
Proof using.
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve wf_sort_rule' : judgment.

Lemma wf_term_rule' : forall l c t,
    wf_sort l c t ->
    wf_rule l ({| c |- t}).
Proof using.
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve wf_term_rule' : judgment.

Lemma le_sort_rule' : forall l c t1 t2,
    wf_sort l c t1 ->
    wf_sort l c t2 ->
    wf_rule l ({< c |- t1 <# t2}).
Proof using.
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve le_sort_rule' : judgment.

Lemma le_term_rule' : forall l c e1 e2 t,
    wf_term l c e1 t ->
    wf_term l c e2 t ->
    wf_rule l ({< c |- e1 <# e2 .: t}).
Proof using.
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve le_term_rule' : judgment.

Hint Resolve wf_lang_nil : judgment.

Lemma wf_lang_cons' : forall l r, wf_rule l r -> wf_lang (r::l).
Proof using.
  eauto with judgment judgment_constructors.
Qed.
Hint Resolve wf_lang_cons' : judgment.



Lemma mono_n l'
  :  (forall (l : lang) c t1 t2,
        le_sort l c t1 t2 -> wf_lang (l' ++ l) ->
        le_sort (l'++l) c t1 t2)
    /\ (forall (l : lang) c s1 s2 c',
           le_subst l c s1 s2 c' ->
           wf_lang (l' ++ l) ->
           le_subst (l'++l) c s1 s2 c')
    /\ (forall (l : lang) c e1 e2 t,
           le_term l c e1 e2 t ->
           wf_lang (l' ++ l) ->
           le_term (l'++l) c e1 e2 t)
    /\ (forall (l : lang) c t,
           wf_sort l c t -> wf_lang (l' ++ l) -> wf_sort (l'++l) c t)
    /\ (forall (l : lang) c s c',
           wf_subst l c s c' -> wf_lang (l' ++ l) -> wf_subst (l'++l) c s c')
    /\ (forall (l : lang) c e t,
           wf_term l c e t -> wf_lang (l' ++ l) -> wf_term (l'++l) c e t)
    /\ (forall (l : lang) c,
           wf_ctx l c -> wf_lang (l' ++ l) ->  wf_ctx (l'++l) c).
Proof using .
  elim: l'; simpl;
    try by repeat match goal with |- _/\_ => split end;
    intros; rewrite ?constr_shift0 ?map_constr_shift0.
  intros.
  repeat match goal with |- _/\_ => split end;
    intros.
  all: by eapply mono;
  [eapply H; auto; inversion H1; apply: wf_rule_lang; eauto|
    by inversion H1].
Qed.

   
Scheme wf_rule_lang_ind := Induction for wf_rule Sort Prop
  with wf_lang_lang_ind := Induction for wf_lang Sort Prop.



Ltac suff_to_use H :=
   match goal with
    | |- ?T =>
      let T' := type of H in
      suff: T = T' => [-> //|]; f_equal
   end.


Lemma add_inj_left a b c : c + a = c + b -> a = b.
Proof.
  elim: c => //; eauto.
Qed.

Lemma inj_constr_shift e e' n : e %! n == e' %! n -> e == e'.
Proof.
  elim: e e' n; intros until e'; case: e'; simpl; auto.
  intro_to is_true.
  case /eqP.
  move /add_inj_left => ->.
  elim: l H l0; intros until l0; case: l0; simpl; auto.
  - move => a l; inversion.
  - inversion.
  - move: H0; simpl; case => H00 H01.
    move => a0 l0; inversion.
    apply /eqP; f_equal.
    f_equal.
    apply /eqP.
    apply: H00.
    apply /eqP; eauto.
    suff: (con n0 l == con n0 l0); [by case /eqP|].
    apply: H; eauto.
Qed.

Lemma inj_map_constr_shift c c' n : c::%! n == c' ::%! n -> c == c'.
Proof using .
  elim: c c'; intros until c'; case: c'; simpl; auto.
  intro_to is_true.
  case /eqP => /eqP => aeq /eqP => leq.
  apply /eqP; f_equal; apply /eqP.
  apply: inj_constr_shift; eauto.
  eauto.
Qed.

Ltac solve_subpar_eq_surjective :=
  match goal with
      | |- ?c ::%! _ = ?c' ::%! _ => 
        suff: c = c' => [-> //|]
      | |- ?e %! _ = ?e'%! _ => 
        suff: e = e' => [-> //|]
      end;
      apply /eqP;
      first[ apply: inj_map_constr_shift | apply: inj_constr_shift];
      apply /eqP;
      repeat match goal with H : _ = _ |- _ => move: H end;
      rewrite ?map_constr_shift_shift ?constr_shift_shift; eauto.


Lemma first_rule_wf l a : wf_lang (a :: l) -> wf_rule (a :: l) a.
Proof using .
  inversion. eapply mono_rule; eauto with judgment.
Qed.


(*TODO: will eventually want a library of better induction schemes for same reason I wanted parameters*)

(* TODO: move to utils*)
Lemma nth_error_size_lt {A} (l : seq A) n e : List.nth_error l n = Some e -> n < size l.
Proof.
  elim: n l => [| n IH];case; simpl; auto; try done.
Qed.

  
Ltac wf_to_ctx_from_rule :=
  intro_to is_true;
  move /rule_in_wf;
  let H := fresh in
  move => H;
  match goal with
    H : ?E, H' : ?E -> _ |- _ =>
    specialize (H' H)
  end;
  inversion H.
