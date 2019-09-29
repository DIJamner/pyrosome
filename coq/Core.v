
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Load Exp.

(* We could embed well-scopedness in bool, but well-typedness can be undecideable,
   so we leave it in Prop.
   Some constructors take in more presuppositions than strictly necessary
   (i.e. they can be derived from other arguments). This is a conscious design choice.
   It is easier to devise secondary "constructor" functions that perform these
   derivations than to do the mutually inductive proof that such derivations exist.
 *)
Inductive wf_sort {p} : lang p -> ctx p -> exp p -> Prop :=
| wf_sort_by : forall l c t,
    wf_lang l ->
    List.In ({| c|- t}) l ->
    wf_sort l c t
| wf_sort_subst : forall l c s c' t',
    wf_subst l c s c' ->
    wf_sort l c' t' ->
    wf_sort l c t'[/s/]
with le_sort {p} : lang p -> ctx p -> ctx p -> exp p -> exp p -> Prop :=
| le_sort_by : forall l c1 c2 t1 t2,
    wf_lang l ->
    List.In ({< c1 <# c2 |- t1 <# t2}) l ->
    le_sort l c1 c2 t1 t2
| le_sort_subst : forall l c1 c2 s1 s2 c1' c2' t1' t2',
    le_subst l c1 c2 s1 s2 c1' c2' ->
    le_sort l c1' c2' t1' t2' ->
    le_sort l c1 c2 t1'[/s1/] t2'[/s2/]
| le_sort_refl : forall l c t,
    wf_lang l ->
    List.In ({| c |- t }) l ->
    le_sort l c c t t
| le_sort_trans : forall l c1 c12 c2 t1 t12 t2,
    le_sort l c1 c12 t1 t12 ->
    le_sort l c12 c2 t12 t2 ->
    le_sort l c1 c2 t1 t2
with wf_term {p} : lang p -> ctx p -> exp p -> exp p -> Prop :=
| wf_term_by : forall l c e t,
    wf_lang l ->
    List.In ({| c |- e .: t}) l ->
    wf_term l c e t
| wf_term_subst : forall l c s c' e' t',
    wf_subst l c s c' ->
    wf_term l c' e' t' ->
    wf_term l c e'[/s/] t'[/s/]
(* terms can be lifted to greater (less precise) types,
   but not the other way around
 *)
| wf_term_conv : forall l c e t c' t',
    wf_term l c e t ->
    le_sort l c c' t t' ->
    wf_term l c' e t'
with le_term {p} : lang p ->
                   ctx p -> ctx p ->
                   exp p -> exp p ->
                   exp p -> exp p -> Prop :=
| le_term_by : forall l c1 c2 e1 e2 t1 t2,
    wf_lang l ->
    List.In ({< c1 <# c2|- e1 <# e2 .: t1 <# t2}) l ->
    le_term l c1 c2 e1 e2 t1 t2
| le_term_subst : forall l c1 c2 s1 s2 c1' c2' e1' e2' t1' t2',
    le_subst l c1 c2 s1 s2 c1' c2' ->
    le_term l c1' c2' e1' e2' t1' t2' ->
    le_term l c1 c2 e1'[/s1/] e2'[/s2/] t1'[/s1/] t2'[/s2/]
| le_term_refl : forall l c e t,
    wf_lang l ->
    List.In ({| c |- e .: t }) l ->
    le_term l c c e e t t
| le_term_trans : forall l c1 c12 c2 e1 e12 e2 t1 t12 t2,
    le_term l c1 c12 e1 e12 t1 t12 ->
    le_term l c12 c2 e12 e2 t12 t2 ->
    le_term l c1 c2 e1 e2 t1 t2
(* Conversion:

c1  < c2  |- e1 < e2 : t1  < t2   ||
/\    /\               /\    /\   ||
c1' < c2' |- e1 < e2 : t1' < t2'  \/
*)
| le_term_conv : forall l c1 c2 e1 e2 t1 t2 c1' c2' t1' t2',
    le_sort l c1' c2' t1' t2' ->
    le_term l c1 c2 e1 e2 t1 t2 ->
    le_sort l c1 c1' t1 t1' ->
    le_sort l c2 c2' t2 t2' ->
    le_term l c1' c2' e1 e2 t1' t2'
with wf_subst {p} : lang p -> ctx p -> subst p ->  ctx p -> Prop :=
| wf_subst_nil : forall l c,
    wf_ctx l c ->
    wf_subst l c [::] [::]
| wf_subst_sort : forall l c s c' t,
    wf_subst l c s c' ->
    wf_sort l c t ->
    wf_subst l c (t::s) c'
| wf_subst_term : forall l c s c' e t,
    wf_subst l c s c' ->
    wf_term l c e t[/s/] ->
    wf_subst l c (e::s) (term_var t::c')
with le_subst {p} : lang p ->
                    ctx p -> ctx p ->
                    subst p -> subst p ->
                    ctx p -> ctx p -> Prop :=
| le_subst_nil : forall l c1 c2,
    le_ctx l c1 c2 ->
    le_subst l c1 c2 [::] [::] [::] [::]
| le_subst_sort : forall l c1 c2 s1 s2 c1' c2' t1 t2,
    le_subst l c1 c2 s1 s2 c1' c2' ->
    le_sort l c1 c2 t1 t2 ->
    le_subst l c1 c2 (t1::s1) (t2::s2) (sort_var::c1') (sort_var::c2')
| le_subst_term : forall l c1 c2 s1 s2 c1' c2' e1 e2 t1 t2,
    le_subst l c1 c2 s1 s2 c1' c2' ->
    le_term l c1 c2 e1 e2 t1[/s1/] t2[/s1/] ->
    le_subst l c1 c2 (e1::s1) (e2::s2) (term_var t1::c1') (term_var t2 :: c2')
with wf_ctx_var {p} : lang p -> ctx p -> ctx_var p -> Prop :=
| wf_sort_var : forall l c,
    wf_ctx l c ->
    wf_ctx_var l c sort_var
| wf_term_var : forall l c t,
    wf_sort l c t ->
    wf_ctx_var l c (term_var t)
with le_ctx_var {p} : lang p -> ctx p -> ctx p -> ctx_var p -> ctx_var p -> Prop :=
| le_sort_var : forall l c1 c2,
    le_ctx l c1 c2 ->
    le_ctx_var l c1 c2 sort_var sort_var
| le_term_var : forall l c1 c2 t1 t2,
    le_sort l c1 c2 t1 t2 ->
    le_ctx_var l c1 c2 (term_var t1) (term_var t2)
with wf_ctx {p} : lang p -> ctx p -> Prop :=
| wf_ctx_nil : forall l, wf_lang l -> wf_ctx l [::]
| wf_ctx_cons : forall l c v,
    wf_ctx_var l c v ->
    wf_ctx l (v::c)
with le_ctx {p} : lang p -> ctx p -> ctx p -> Prop :=
| le_ctx_nil : forall l, wf_lang l -> le_ctx l [::] [::]
| le_ctx_cons : forall l c1 c2 v1 v2,
    le_ctx_var l c1 c2 v1 v2 ->
    le_ctx l (v1::c1) (v2::c2)
with wf_rule {p} : lang p -> rule p -> Prop :=
| wf_sort_rule : forall l c t,
    wf_ctx l c ->
    (* TODO: require t (prefix) not in thy? interferes with monotonicity *)
    wf_rule l ({| c |- t})
| wf_term_rule : forall l c e t,
    wf_ctx l c ->
    wf_sort l c t ->
    (* TODO: require e (prefix) not in thy? interferes with monotonicity *)
    wf_rule l ({| c |- e .: t})
| le_sort_rule : forall l c1 c2 t1 t2,
    le_ctx l c1 c2 ->
    wf_sort l c1 t1 ->
    wf_sort l c2 t2 ->
    wf_rule l ({< c1 <# c2 |- t1 <# t2})
| le_term_rule : forall l c1 c2 e1 e2 t1 t2,
    le_sort l c1 c2 t1 t2 ->
    wf_term l c1 e1 t1 ->
    wf_term l c2 e2 t2 ->
    wf_rule l ({< c1 <# c2 |- e1 <# e2 .: t1 <# t2})
with wf_lang {p} : lang p -> Prop :=
| wf_lang_nil : wf_lang [::]
| wf_lang_cons : forall l r, wf_rule l r -> wf_lang (r::l).
Hint Constructors wf_sort.
Hint Constructors wf_term.
Hint Constructors wf_subst.
Hint Constructors wf_ctx_var.
Hint Constructors wf_ctx.
Hint Constructors wf_rule.
Hint Constructors wf_lang.
Hint Constructors le_sort.
Hint Constructors le_term.
Hint Constructors le_subst.
Hint Constructors le_ctx_var.
Hint Constructors le_ctx.

Ltac intro_term :=
  match goal with
  | [|- lang _ -> _] => intro
  | [|- exp _ -> _] => intro
  | [|- ctx _ -> _] => intro
  | [|- ctx_var _ -> _] => intro
  | [|- rule _ -> _] => intro
  | [|- subst _ -> _] => intro
  end.

Ltac construct_with t :=
  constructor; apply: t; eauto.
  
Ltac solve_wf_with t :=
  solve [ (constructor + idtac); apply: t; eauto
        | intro_term; solve_wf_with t
        | move => _; solve_wf_with t].

(* well-formed language suppositions *)
Lemma wf_ctx_lang  {p} (l : lang p) c (wf : wf_ctx l c) : wf_lang l
with wf_ctx_var_lang  {p} (l : lang p) c v (wf : wf_ctx_var l c v) : wf_lang l
with wf_sort_lang  {p} (l : lang p) c t (wf : wf_sort l c t) : wf_lang l.
  all: case: wf => //=.
  solve_wf_with wf_ctx_var_lang.
  solve_wf_with wf_ctx_lang.
  solve_wf_with wf_sort_lang.
  solve_wf_with wf_sort_lang.
Qed.

Lemma wf_term_lang  {p} (l : lang p) c e t
      (wf : wf_term l c e t) : wf_lang l
with wf_subst_lang  {p} (l : lang p) c s c'
           (wf : wf_subst l c s c') : wf_lang l.
  all: case: wf => //=.
  solve_wf_with wf_term_lang.
  repeat intro_term.
  move => wft wfs.
  apply: wf_term_lang; eauto.
  solve_wf_with (@wf_ctx_lang p).
  solve_wf_with (@wf_sort_lang p).
  solve_wf_with wf_term_lang.
Qed.

Lemma wf_rule_lang {p} (l : lang p) r
      (wf : wf_rule l r) : wf_lang l.
Proof.
  all: case: wf => //=.
  solve_wf_with (@wf_ctx_lang p).
  solve_wf_with (@wf_sort_lang p).
  solve_wf_with (@wf_sort_lang p).
  solve_wf_with (@wf_term_lang p).
Qed.

Lemma wf_sort_mono {p} (l : lang p) r c t : wf_rule l r -> wf_sort l c t -> wf_sort (r::l) c t
with wf_subst_mono {p} (l : lang p) r c s c'
     : wf_rule l r -> wf_subst l c s c' -> wf_subst (r::l) c s c'
with wf_term_mono {p} (l : lang p) r c e t
     : wf_rule l r -> wf_term l c e t -> wf_term (r::l) c e t
with le_ctx_mono {p} (l : lang p) r c1 c2
     : wf_rule l r -> le_ctx l c1 c2 -> le_ctx (r::l) c1 c2
with le_ctx_var_mono {p} (l : lang p) r c1 c2 v1 v2
     : wf_rule l r -> le_ctx_var l c1 c2 v1 v2 -> le_ctx_var (r::l) c1 c2 v1 v2
with le_sort_mono {p} (l : lang p) r c1 c2 t1 t2
     : wf_rule l r -> le_sort l c1 c2 t1 t2 -> le_sort (r::l) c1 c2 t1 t2
with le_subst_mono {p} (l : lang p) r c1 c2 s1 s2 c1' c2'
     : wf_rule l r -> le_subst l c1 c2 s1 s2 c1' c2' -> le_subst (r::l) c1 c2 s1 s2 c1' c2'
with le_term_mono {p} (l : lang p) r c1 c2 e1 e2 t1 t2
     : wf_rule l r -> le_term l c1 c2 e1 e2 t1 t2 -> le_term (r::l) c1 c2 e1 e2 t1 t2.
Proof.
 - move => wfr wfs.
   move: wfr.
   refine (match wfs with
           | wf_sort_by _ _ _ _ _ => _
           | wf_sort_subst _ _ _ _ _ _ _ => _
           end).
   + constructor. auto. move => //=. apply: List.in_cons => //=.
   +  move => wfr.
      apply: wf_sort_subst.
      apply: wf_subst_mono => //=. apply w.
      apply: wf_sort_mono => //=.
 - move => wfr wfsb.
   move: wfr.
   refine (match wfsb with
           | wf_subst_nil _ _ _ => _
           | wf_subst_sort _ _ _ _ _ _ _ => _
           | wf_subst_term _ _ _ _ _ _ _ _ => _
           end).
   + auto.
   + repeat intro_term.
     move => wfr.
     apply: wf_subst_sort.
     apply: wf_subst_mono => //=.
     apply: wf_sort_mono => //=.
   + repeat intro_term.
     move => wfr.
     apply: wf_subst_term.
     apply: wf_subst_mono => //=.
     apply: wf_term_mono => //=.
 - move => wfr wft.
   move: wfr.
   refine (match wft with
           | wf_term_by _ _ _ _ _ _ => _
           | wf_term_subst _ _ _ _ _ _ _ _ => _
           | wf_term_conv _ _ _ _ _ _ _ _ => _ end).
   + constructor; auto;
       apply: List.in_cons => //=.
   + Print wf_term_subst. 
     (*
       wf_term_subst : forall (l : lang p) (c : ctx p) (s : subst p) (c' : ctx p) (e' t' : exp p),
                       wf_subst l c s c' -> wf_term l c' e' t' -> wf_term l c e' [/s /] t' [/s /]  

      *)
     intros; apply: (@wf_term_subst p (r :: l0) c0 s c1 e0 e1); auto.
   + intros; apply: (@wf_term_conv p (r :: l0) c0 e0 e1); auto.
 - move => wfr wf.
   move: wfr.
   refine (match wf with
           | le_ctx_nil _ _ => _
           | le_ctx_cons _ _ _ _ _ _ => _ end).
   + constructor; auto; apply: List.in_cons => //=.
   + intros; apply: le_ctx_cons. auto.
 - move => wfr wf.
   move: wfr.
   refine (match wf with
           | le_term_var _ _ _ _ _ _ => _
           | le_sort_var _ _ _ _ => _ end).
   + constructor; auto; apply: List.in_cons => //=.
   + intros; apply: le_term_var. auto.
 - move => wfr wf; move: wfr.
   refine (match wf with
           | le_sort_by _ _ _ _ _ _ _ => _
           | le_sort_subst _ _ _ _ _ _ _ _ _ _ _ => _
           | le_sort_refl _ _ _ _ _ => _
           | le_sort_trans _ _ _ _ _ _ _ _ _ => _ end).
   + constructor; auto; apply: List.in_cons => //=.
   + intros; apply: (@le_sort_subst p (r :: l0) c c0 s s0 c3 c4); auto.
   + intros; apply: (@le_sort_refl p (r :: l0) c e); auto;
       apply: List.in_cons => //=.
   + intros; apply: (@le_sort_trans p (r :: l0) c c0 c3 e e0 e1); auto.
 - move => wfr wf; move: wfr.
   refine (match wf with
           | le_subst_nil _ _ _ _ => _
           | le_subst_sort _ _ _ _ _ _ _ _ _ _ _ => _
           | le_subst_term _ _ _ _ _ _ _ _ _ _ _ _ _ => _ end).
   + constructor; auto. 
   + intros; apply: le_subst_sort; auto. 
   + intros; apply: le_subst_term; auto.
 - move => wfr wf; move: wfr.
   refine (match wf with
           | le_term_by _ _ _ _ _ _ _ _ _ => _
           | le_term_subst _ _ _ _ _ _ _ _ _ _ _ _ _ => _
           | le_term_refl _ _ _ _ _ _ => _
           | le_term_trans _ _ _ _ _ _ _ _ _ _ _ _ => _
           | le_term_conv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => _ end).
   + constructor; auto; apply: List.in_cons => //=.
   + intros; apply: (@le_term_subst p (r :: l0) c c0 s s0 c3 c4); auto.
   + intros; apply: le_term_refl; auto;
       apply: List.in_cons => //=.
   + intros; apply: (@le_term_trans p (r :: l0) c c0 c3 e e0 e3 e4 e5); auto.
   + intros; apply: (@le_term_conv p (r :: l0) c c0 e e0 e3 e4); auto.
     Show Proof.
Qed.  
     
   
Lemma le_ctx_wf_l  {p} (l : lang p) c1 c2 (wf : le_ctx l c1 c2) : wf_ctx l c1
with le_ctx_var_wf_l  {p} (l : lang p) c1 c2 v1 v2
                      (wf : le_ctx_var l c1 c2 v1 v2) : wf_ctx_var l c1 v1
with le_sort_wf_l  {p} (l : lang p) c1 c2 t1 t2
                   (wf : le_sort l c1 c2 t1 t2) : wf_sort l c1 t1.
  all: case: wf => //=.
  solve_wf_with (@wf_ctx_nil p).
  solve_wf_with le_ctx_var_wf_l.
  solve_wf_with le_ctx_wf_l.
  solve_wf_with le_sort_wf_l.
  (* depends on monotonicity *)
Qed.

(* TODO: this isn't true in general if I add *)
Lemma rule_in_wf {p} (l : lang p) r : wf_lang l -> List.In r l -> wf_rule l r.
Qed.

Lemma wf_sort_ctx {p} (l : lang p) c t
      (wf : wf_sort l c t) : wf_ctx l c.
Proof.
  all: case: wf => //=.
Qed.

(* TODO: transitivity proofs *)
(* TODO: monotonicity proofs *)  

(* =======================
   OLD: update to work with present definition
===============================*)

Lemma wf_ctx_var_lang  {p} (l : lang p) c1 c2 v1 v2
           (wf : wf_ctx_var l c1 c2 v1 v2) : wf_lang l.
  case: wf => //=.
Qed.
Hint Immediate wf_ctx_var_lang : wf_hints.
Lemma wf_sort_lang  {p} (l : lang p) c1 c2 t1 t2
           (wf : wf_sort l c1 c2 t1 t2) : wf_lang l.
  case: wf => //=.
Qed.
Hint Immediate wf_sort_lang : wf_hints.

Hint Immediate wf_term_lang : wf_hints.
Lemma wf_subst_lang  {p} (l : lang p) c1 c2 s1 s2 c1' c2'
           (wf : wf_subst l c1 c2 s1 s2 c1' c2') : wf_lang l.
  case: wf => //=.
Qed.
Hint Immediate wf_subst_lang : wf_hints.
Lemma wf_rule_lang  {p} (l : lang p) r
           (wf : wf_rule l r) : wf_lang l.
  case: wf => //=.
Qed.
Hint Immediate wf_rule_lang : wf_hints.

(* well-formed context suppositions *)
Lemma wf_sort_ctx  {p} (l : lang p) c1 c2 t1 t2
           (wf : wf_sort l c1 c2 t1 t2) : wf_ctx l c1 c2.
  case: wf => //=.
Qed.
Hint Immediate wf_sort_ctx : wf_hints.
Lemma wf_ctx_var_ctx  {p} (l : lang p) c1 c2 v1 v2
           (wf : wf_ctx_var l c1 c2 v1 v2) : wf_ctx l c1 c2.
  case: wf => //= l' c1' c2' t1 t2 _ /wf_sort_ctx //=.
Qed.
Hint Immediate wf_ctx_var_ctx : wf_hints.
Lemma wf_term_ctx  {p} (l : lang p) c1 c2 e1 e2 t1 t2
           (wf : wf_term l c1 c2 e1 e2 t1 t2) : wf_ctx l c1 c2.
  case: wf => //=.
Qed.
Hint Immediate wf_term_ctx : wf_hints.
Lemma wf_subst_ctx  {p} (l : lang p) c1 c2 s1 s2 c1' c2'
           (wf : wf_subst l c1 c2 s1 s2 c1' c2') : wf_ctx l c1 c2.
  case: wf => //=.
Qed.
Hint Immediate wf_subst_ctx : wf_hints.
Lemma wf_subst_ctx_out  {p} (l : lang p) c1 c2 s1 s2 c1' c2'
           (wf : wf_subst l c1 c2 s1 s2 c1' c2') : wf_ctx l c1' c2'.
  case: wf => //=.
Qed.
Hint Immediate wf_subst_ctx_out : wf_hints.

(* well-formed sort presuppositions *)
Lemma wf_term_sort {p} (l : lang p) c1 c2 e1 e2 t1 t2
           (wf : wf_term l c1 c2 e1 e2 t1 t2) : wf_sort l c1 c2 t1 t2.
  case: wf => //=.
Qed.
Hint Immediate wf_term_sort : wf_hints.

(* TODO: what is the best way to handle these tactics?
   I am going to want to improve them later, but dont want to rewrite all of them.
   I'm attempting the hint database now. It's possible the tactics won't be necessary?
*)

(* TODO: should I have another variant w/ the same parameter improvement
   but keeping all of the presuppositions?
   I could call the m wf...intro and wf...elim)*)
Variant wf_ctx_ {p} (l : lang p) : ctx p -> ctx p -> Prop :=
| wf_ctx_nil_ : wf_lang l -> wf_ctx_ l [::] [::]
| wf_ctx_cons_ : forall c1 c2 v1 v2,
    wf_ctx_var l c1 c2 v1 v2 ->
    wf_ctx_ l (v1::c1) (v2::c2).
Hint Constructors wf_ctx_.

Variant wf_ctx_var_ {p} (l : lang p) (c1 c2 : ctx p) : ctx_var p -> ctx_var p -> Prop :=
| wf_sort_var_ : wf_ctx l c1 c2 -> wf_ctx_var_ l c1 c2 sort_var sort_var
| wf_term_var_ : forall t1 t2,
    wf_sort l c1 c2 t1 t2 ->
    wf_ctx_var_ l c1 c2 (term_var t1) (term_var t2).
Hint Constructors wf_ctx_var_.

Variant wf_sort_ {p} (l : lang p) (c1 c2 : ctx p) : poly_fix p -> poly_fix p -> Prop :=
| wf_sort_by_ : forall t1 t2 s1 s2 c1' c2',
    (* TODO: remove this presupposition *)
    wf_sort l c1 c2 t1 t2 ->
    wf_subst l c1 c2 s1 s2 c1' c2' ->
    List.In ({r c1' <# c2'|- t1 <# t2}%rule) l ->
    wf_sort_ l c1 c2 (exp_subst t1 s1) (exp_subst t2 s2)
| wf_sort_trans_ : forall c12 t1 t12 t2,
    (* well-formed input *)
    wf_sort l c1 c12 t1 t12 ->
    wf_sort l c12 c2 t12 t2 ->
    wf_sort_ l c1 c2 t1 t2.
Hint Constructors wf_sort_.


Variant wf_term_ {p} (l : lang p) (c1 c2 : ctx p)
  : poly_fix p -> poly_fix p -> poly_fix p -> poly_fix p -> Prop :=
| wf_term_by_ : forall e1 e2 t1 t2 s1 s2 c1' c2',
    wf_subst l c1 c2 s1 s2 c1' c2' ->
    List.In ({r c1' <# c2' |- e1 <# e2.: t1 <# t2}%rule) l ->
    wf_term_ l c1 c2 (exp_subst e1 s1) (exp_subst e2 s2) (exp_subst t1 s1) (exp_subst t2 s2)
| wf_term_trans_ : forall c12 e1 e12 e2 t1 t12 t2,
    wf_term l c1 c12 e1 e12 t1 t12 ->
    wf_term l c12 c2 e12 e2 t12 t2 ->
    wf_term_ l c1 c2 e1 e2 t1 t2
(* TODO: these rules are experimental; check *)
| wf_term_conv_r_ : forall c12 e1 e2 t1 t12 t2,
    wf_term l c1 c12 e1 e2 t1 t12 ->
    wf_sort l c12 c2 t12 t2 ->
    wf_term_ l c1 c2 e1 e2 t1 t2
| wf_term_conv_l_ : forall c12 e1 e2 t1 t12 t2,
    wf_term l c12 c2 e1 e2 t12 t2 ->
    wf_sort l c1 c12 t1 t12 ->
    wf_term_ l c1 c2 e1 e2 t1 t2.
Hint Constructors wf_sort_.

Ltac hypothesize :=
  try match goal with
        [|- _ -> _] => let H := fresh in move => H; hypothesize
      end.

Ltac solve_wf_lang :=
  match goal with
  | [H : wf_ctx ?l _ _ |- wf_lang ?l] => apply: wf_ctx_lang; exact H
  | [H : wf_ctx_var ?l _ _ _ _ |- wf_lang ?l] => apply: wf_ctx_var_lang; exact H
  | [H : wf_sort ?l _ _ _ _ |- wf_lang ?l] => apply: wf_sort_lang; exact H
  | [H : wf_term ?l _ _ _ _ _ _ |- wf_lang ?l] => apply: wf_term_lang; exact H
  | [H : wf_subst ?l _ _ _ _ _ _ |- wf_lang ?l] => apply: wf_subst_lang; exact H
  | [H : wf_rule ?l _ |- wf_lang ?l] => apply: wf_rule_lang; exact H
  end.

Ltac solve_wf_ctx :=
  match goal with
  | [H : wf_ctx_var ?l ?c1 ?c2 _ _ |- wf_ctx ?l ?c1 ?c2] => apply: wf_ctx_var_ctx; exact H
  | [H : wf_sort ?l ?c1 ?c2 _ _ |- wf_ctx ?l ?c1 ?c2] => apply: wf_sort_ctx; exact H
  | [H : wf_term ?l ?c1 ?c2 _ _ _ _ |- wf_ctx ?l ?c1 ?c2] => apply: wf_term_ctx; exact H
  | [H : wf_subst ?l ?c1 ?c2 _ _ _ _ |- wf_ctx ?l ?c1 ?c2] => apply: wf_subst_ctx; exact H
  | [H : wf_subst ?l _ _ _ _ ?c1 ?c2 |- wf_ctx ?l ?c1 ?c2] => apply: wf_subst_ctx_out; exact H
  end.

Ltac constr_wf :=
  apply: wf_sort_by
    + apply: wf_sort_trans
    + apply: wf_ctx_nil
    + apply: wf_ctx_cons
    + apply: wf_sort_var
    + apply: wf_term_var
    + apply: wf_term_by
    + apply: wf_term_trans
    + apply: wf_term_conv_l
    + apply: wf_term_conv_r
    (* good variants *)
    + apply: wf_ctx_nil_
    + apply: wf_ctx_cons_
    + apply: wf_sort_by_
    + apply: wf_sort_trans_
    + apply: wf_sort_var_
    + apply: wf_term_var_
    + apply: wf_term_by_
    + apply: wf_term_trans_
    + apply: wf_term_conv_l_
    + apply: wf_term_conv_r_
             + idtac. 
  
Ltac solve_wf :=
  by hypothesize;
  constr_wf;
  do [solve_wf_lang
     | solve_wf_ctx
     | eauto].
  
Lemma wf_ctx_conv p (l : lang p) c1 c2 : wf_ctx l c1 c2 <-> wf_ctx_ l c1 c2.
Proof.
  split; case; solve_wf.
Qed.
Hint Resolve <- wf_ctx_conv 0 : wf_hints.
Coercion ctx_coerce p (l : lang p) c1 c2 := fst (wf_ctx_conv l c1 c2).

Lemma wf_ctx_var_conv p (l : lang p) c1 c2 v1 v2
  : wf_ctx_var l c1 c2 v1 v2 <-> wf_ctx_var_ l c1 c2 v1 v2.
Proof.
  split; case; solve_wf.
Qed.
Hint Resolve <- wf_ctx_var_conv 0 : wf_hints.
Coercion ctx_var_coerce p (l : lang p) c1 c2 v1 v2 := fst (wf_ctx_var_conv l c1 c2 v1 v2).

Fixpoint wf_ctx_to_trans' (n : nat) p (l : lang p) (c1 c2 c3 :ctx p) {struct n}
  : n = 2 * size c1 -> wf_ctx l c1 c2 -> wf_ctx l c2 c3 -> wf_ctx l c1 c3
with wf_ctx_var_to_trans' (n : nat) p (l : lang p) c1 c2 c3 v1 v2 v3 {struct n}
     : n = (2 * size c1).+1 ->
       wf_ctx_var l c1 c2 v1 v2 ->
       wf_ctx_var l c2 c3 v2 v3 ->
       wf_ctx_var l c1 c3 v1 v3.
Proof.
  - refine (match n as n' return n' = 2 * size c1 -> _ -> _ -> _ with
              | 0 => _
              | S n0 => _
            end).
    + case c1.
      * move => _ wf2 wf3.
        inversion wf2.
        rewrite -H2 in wf3.
        inversion wf3.
        constructor => //=.
      * move => c l' neq; inversion neq.
    + move => neq wf1 wf2.
      inversion wf1.
      rewrite -H2 in wf2;
        inversion wf2;
      apply wf_ctx_conv;
      constructor => //=.
      rewrite -H4 in wf2;
        inversion wf2.
      apply wf_ctx_conv;
        constructor => //=.
      apply: (wf_ctx_var_to_trans' n0) => //=.
      rewrite -H3 in neq.
      simpl in neq.
      rewrite mulnSr in neq.
      rewrite addn2 in neq.
      inversion neq.
      done.
      exact H1.
      done.
  - refine (match n as n' return n' = (2 * size c1).+1 -> _ -> _ -> _ with
              | 0 => _
              | S n0 => _
            end).
    + move => neq;
      inversion neq.
    + move => neq wf1 wf2; inversion neq.
      inversion wf1;
      rewrite <- H6 in wf2;
      inversion wf2;
        apply wf_ctx_var_conv;
        constructor.
      * apply: (wf_ctx_to_trans' n0) => //=.        
        exact H1.
        done.
      * have wfs13 : wf_sort l c1 c3 t1 t3.
        apply: wf_sort_trans.
        done.
        apply: (wf_ctx_to_trans' n0) => //=.
        apply: wf_sort_ctx; eauto.
        apply: wf_sort_ctx; eauto.
        eauto.
        eauto.
        done.
Qed. 


Lemma wf_ctx_to_trans p (l : lang p) (c1 c2 c3 :ctx p)
  : wf_ctx l c1 c2 -> wf_ctx l c2 c3 -> wf_ctx l c1 c3.
Proof.
  apply: wf_ctx_to_trans' => //=.
Qed.
                                                        
Lemma wf_ctx_var_to_trans p (l : lang p) c1 c2 c3 v1 v2 v3
     : wf_ctx_var l c1 c2 v1 v2 ->
       wf_ctx_var l c2 c3 v2 v3 ->
       wf_ctx_var l c1 c3 v1 v3.
Proof.
  apply: wf_ctx_var_to_trans'; eauto.
Qed.


Lemma wf_sort_conv p (l : lang p) c1 c2 t1 t2
  : wf_sort l c1 c2 t1 t2 <-> wf_sort_ l c1 c2 t1 t2.
Proof.
  split.
  - case; solve_wf.
  - case.
    move => t1' t2' s1 s2 c1' c2' wfs wfsb wfr.
    apply: wf_sort_by; auto; try by solve_wf.
    move => c12 t1' t12 t3' wf1 wf3.
    apply: wf_sort_trans.
    solve_wf.
    apply: wf_ctx_to_trans;
      apply: wf_sort_ctx; eauto.
    eauto.
    eauto.
Qed.
Hint Resolve <- wf_sort_conv 0 : wf_hints.
Coercion sort_coerce p (l : lang p) c1 c2 t1 t2 := fst (wf_sort_conv l c1 c2 t1 t2).

(*TODO: induction principles using wf_sort_, etc
  should _ be inductives? probably
 *)
Lemma wf_sort_monotone p (l : lang p) c1 c2 t1 t2
  : wf_sort l c1 c2 t1 t2 -> forall r, wf_rule l r -> wf_sort (r::l) c1 c2 t1 t2
with wf_subst_monotone p (l : lang p) c1 c2 s1 s2 c1' c2'
     : wf_subst l c1 c2 s1 s2 c1' c2' ->
       forall r, wf_rule l r -> wf_subst (r::l) c1 c2 s1 s2 c1' c2'.
Proof.
  - case /wf_sort_conv.
    move => t1' t2' s1 s2 c1'' c2''.
    move => wfs wfsb lin r wfr.
    rewrite wf_sort_conv.
    apply: wf_sort_by_.
    apply: wf_sort_monotone; done.
    apply: wf_subst_monotone; try done.
    eassumption.
    
    apply: IH; done.
    
    (*TODO: needs to be mutual with subst monotone? *)
    

Lemma wf_rule_term p (l : lang p) c1 c2 e1 e2 t1 t2
  : wf_lang l -> List.In ({rc1 <# c2 |- e1 <# e2 .: t1 <# t2}) l -> wf_term l c1 c2 e1 e2 t1 t2.
Proof.
  elim: l; [done|].
  move => r l' IH wfl.
  case.
  - move => req.
    inversion wfl.
    rewrite req in H2.
    inversion H2.
    (*TODO: prove monotonicity of language extension *)
i
Lemma wf_term_conv p (l : lang p) c1 c2 e1 e2 t1 t2
  : wf_term l c1 c2 e1 e2 t1 t2 <-> wf_term_ l c1 c2 e1 e2 t1 t2.
Proof.
  split; case; try solve_wf.
  - hypothesize.
    apply:wf_term_conv_r_; eauto.
    (*TODO: build into solve_wf*)
  - hypothesize.
    apply:wf_term_conv_l_; eauto.
  - hypothesize.
    apply:wf_term_by; eauto.
    apply: wf_subst_lang; eauto.
    apply: wf_subst_ctx; eauto.
    move => l' c1' c12 c2' e1' e2' t1' t12 t2'.
    move => wfl wfc wfs wft wfs'.
    apply:wf_term_conv_r_; eauto.
    apply wft.
Hint Resolve <- wf_term_conv 0 : wf_hints.
Coercion term_coerce p (l : lang p) c1 c2 e1 e2 t1 t2 := fst (wf_term_conv l c1 c2 e1 e2 t1 t2).
