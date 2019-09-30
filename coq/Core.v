
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Load CoreDefs.

(* Cheat Sheet

Syntax:
polynomial
lang p
exp p
ctx p
ctx_var p
rule p
subst p

Judgments:
wf_sort
le_sort
wf_term
le_term
wf_subst
le_subst
wf_ctx_var
le_ctx_var
wf_ctx
le_ctx
wf_rule
wf_lang
 *)

(* Tactics *)

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


(* Note: Fixpoint vs Lemma changes the elements chosen to be recursive *)
Fixpoint le_ctx_mono {p} (l : lang p) r c1 c2
                 (wfc : le_ctx l c1 c2)
     : wf_rule l r -> le_ctx (r::l) c1 c2
with le_ctx_var_mono {p} (l : lang p) r c1 c2 v1 v2
                     (wfv : le_ctx_var l c1 c2 v1 v2)
     : wf_rule l r -> le_ctx_var (r::l) c1 c2 v1 v2
with le_sort_mono {p} (l : lang p) r c1 c2 t1 t2
                  (wfs : le_sort l c1 c2 t1 t2)
     : wf_rule l r -> le_sort (r::l) c1 c2 t1 t2
with le_subst_mono {p} (l : lang p) r c1 c2 s1 s2 c1' c2'
                   (wfsb : le_subst l c1 c2 s1 s2 c1' c2')
     : wf_rule l r -> le_subst (r::l) c1 c2 s1 s2 c1' c2'
with le_term_mono {p} (l : lang p) r c1 c2 e1 e2 t1 t2
                  (wft :  le_term l c1 c2 e1 e2 t1 t2)
     : wf_rule l r -> le_term (r::l) c1 c2 e1 e2 t1 t2.
Proof.
  - refine (match wfc with
           | le_ctx_nil _ _ => _
           | le_ctx_cons _ _ _ _ _ _ => _ end).
   + constructor; auto; apply: List.in_cons => //=.
   + intros; apply: le_ctx_cons. auto.
 - refine (match wfv with
           | le_term_var _ _ _ _ _ _ => _
           | le_sort_var _ _ _ _ => _ end).
   + constructor; auto; apply: List.in_cons => //=.
   + intros; apply: le_term_var. auto.
 - refine (match wfs with
           | le_sort_by _ _ _ _ _ _ _ => _
           | le_sort_subst _ _ _ _ _ _ _ _ _ _ _ => _
           | le_sort_refl _ _ _ _ _ => _
           | le_sort_trans _ _ _ _ _ _ _ _ _ => _ end).
   + constructor; auto; apply: List.in_cons => //=.
   + intros; apply: (@le_sort_subst p (r :: l0) c c0 s s0 c3 c4); auto.
   + intros; apply: (@le_sort_refl p (r :: l0) c e); auto;
       apply: List.in_cons => //=.
   + intros; apply: (@le_sort_trans p (r :: l0) c c0 c3 e e0 e1); auto.
 - refine (match wfsb with
           | le_subst_nil _ _ _ _ => _
           | le_subst_sort _ _ _ _ _ _ _ _ _ _ _ => _
           | le_subst_term _ _ _ _ _ _ _ _ _ _ _ _ _ => _ end).
   + constructor; auto. 
   + intros; apply: le_subst_sort; auto. 
   + intros; apply: le_subst_term; auto.
 - refine (match wft with
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
Qed.


Scheme wf_sort_mono_ind := Minimality for wf_sort Sort Prop
  with wf_subst_mono_ind := Minimality for wf_subst Sort Prop
  with wf_term_mono_ind := Minimality for wf_term Sort Prop
  with wf_ctx_mono_ind := Minimality for wf_ctx Sort Prop
  with wf_ctx_var_mono_ind := Minimality for wf_ctx_var Sort Prop.

Combined Scheme mono_ind from
         wf_sort_mono_ind,
         wf_subst_mono_ind,
         wf_term_mono_ind,
         wf_ctx_mono_ind,
         wf_ctx_var_mono_ind.

Lemma wf_sort_subst_term_ctx_ctx_var_mono {p} r
  : (forall (l : lang p) c t, wf_sort l c t -> wf_rule l r -> wf_sort (r::l) c t)
    /\ (forall (l : lang p) c s c', wf_subst l c s c' -> wf_rule l r -> wf_subst (r::l) c s c')
    /\ (forall (l : lang p) c e t,  wf_term l c e t -> wf_rule l r ->  wf_term (r::l) c e t)
    /\ (forall (l : lang p) c,  wf_ctx l c -> wf_rule l r ->  wf_ctx (r::l) c)
    /\ (forall (l : lang p) c v,  wf_ctx_var l c v -> wf_rule l r ->  wf_ctx_var (r::l) c v).
Proof.
  apply: mono_ind; try by eauto;
    try by repeat (constructor; try apply: List.in_cons).
  move => l c e t c' t' wft IH les wfr.
  apply: wf_term_conv; eauto.
  apply: le_sort_mono; auto.
Qed.

Lemma wf_sort_mono {p} (l : lang p) r c t : wf_sort l c t -> wf_rule l r -> wf_sort (r::l) c t.
Proof.
  eapply wf_sort_subst_term_ctx_ctx_var_mono.
Qed.
      
Lemma wf_subst_mono {p} (l : lang p) r c s c'
  : wf_subst l c s c' -> wf_rule l r -> wf_subst (r::l) c s c'.
Proof.
  eapply wf_sort_subst_term_ctx_ctx_var_mono.
Qed.

Lemma wf_term_mono {p} (l : lang p) r c e t
  : wf_term l c e t -> wf_rule l r -> wf_term (r::l) c e t.
Proof.
  eapply wf_sort_subst_term_ctx_ctx_var_mono.
Qed.

Lemma wf_ctx_mono {p} (l : lang p) r c : wf_ctx l c -> wf_rule l r -> wf_ctx (r::l) c.
Proof.
  eapply wf_sort_subst_term_ctx_ctx_var_mono.
Qed.

Lemma wf_ctx_var_mono {p} (l : lang p) r c v
  : wf_ctx_var l c v -> wf_rule l r -> wf_ctx_var (r::l) c v.
Proof.
  eapply wf_sort_subst_term_ctx_ctx_var_mono.
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


Lemma wf_sort_conv {p} (l : lang p) c t : wf_sort l c t <-> wf_sort_ l c t.
Proof.
  split; case; auto.
  - constructor.
    TODO

TODO: place these tactics well wrt wf_..._convs
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
