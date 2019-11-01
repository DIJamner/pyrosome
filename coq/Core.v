
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

(* TODO: change from loads to imports *)
From excomp Require Import Exp CoreDefs.

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
  | [|- seq (rule _) -> _] => intro
  | [|- exp _ -> _] => intro
  | [|- ctx _ -> _] => intro
  | [|- seq (exp _) -> _] => intro
  | [|- rule _ -> _] => intro
  | [|- subst _ -> _] => intro
  end.

Tactic Notation "intro_to" constr(ty) :=
  repeat lazymatch goal with
         | |- ty -> _ => idtac
         | |- ty _ -> _ => idtac
         | |- ty _ _-> _ => idtac
         | |- ty _ _ _ -> _ => idtac
         | |- _ -> _ => intro
         end.

Ltac construct_with t :=
  constructor; apply: t; eauto.
  
Ltac solve_wf_with t :=
  solve [ (constructor + idtac); apply: t; eauto
        | intro_term; solve_wf_with t
        | move => _; solve_wf_with t].

(* well-formed language suppositions *)
Lemma wf_ctx_lang  {p} (l : lang p) c (wf : wf_ctx l c) : wf_lang l
with wf_sort_lang  {p} (l : lang p) c t (wf : wf_sort l c t) : wf_lang l.
  all: case: wf => //=;
  solve_wf_with wf_sort_lang.
Qed.
Hint Immediate wf_ctx_lang.
Hint Immediate wf_sort_lang.

Lemma wf_term_lang  {p} (l : lang p) c e t
      (wf : wf_term l c e t) : wf_lang l
with wf_subst_lang  {p} (l : lang p) c s c'
           (wf : wf_subst l c s c') : wf_lang l.
  all: case: wf => //=;
  try solve_wf_with wf_term_lang.
  repeat intro_term.
  move => wft wfs.
  apply: wf_term_lang; eauto.
  solve_wf_with (@wf_sort_lang p).
  solve_wf_with (@wf_ctx_lang p).
Qed.
Hint Immediate wf_term_lang.
Hint Immediate wf_subst_lang.

Lemma wf_rule_lang {p} (l : lang p) r
      (wf : wf_rule l r) : wf_lang l.
Proof.
  all: case: wf => //=.
  solve_wf_with (@wf_ctx_lang p).
  solve_wf_with (@wf_sort_lang p).
  solve_wf_with (@wf_sort_lang p).
  solve_wf_with (@wf_term_lang p).
Qed.
Hint Immediate wf_rule_lang.


(* TODO: should this hint be used more generally? *)
Local Hint Resolve List.in_cons.

Scheme le_sort_mono_ind := Minimality for le_sort Sort Prop
  with le_subst_mono_ind := Minimality for le_subst Sort Prop
  with le_term_mono_ind := Minimality for le_term Sort Prop
  with le_ctx_mono_ind := Minimality for le_ctx Sort Prop
  with wf_sort_mono_ind := Minimality for wf_sort Sort Prop
  with wf_subst_mono_ind := Minimality for wf_subst Sort Prop
  with wf_term_mono_ind := Minimality for wf_term Sort Prop
  with wf_ctx_mono_ind := Minimality for wf_ctx Sort Prop.

Combined Scheme mono_ind from
         le_sort_mono_ind,
         le_subst_mono_ind,
         le_term_mono_ind,
         le_ctx_mono_ind,
         wf_sort_mono_ind,
         wf_subst_mono_ind,
         wf_term_mono_ind,
         wf_ctx_mono_ind.

Lemma mono {p} r
  : (forall (l : lang p) c1 c2 t1 t2,
        le_sort l c1 c2 t1 t2 -> wf_rule l r -> le_sort (r::l) c1 c2 t1 t2)
    /\ (forall (l : lang p) c1 c2 s1 s2 c1' c2',
           le_subst l c1 c2 s1 s2 c1' c2' ->
           wf_rule l r ->
           le_subst (r::l) c1 c2 s1 s2 c1' c2')
    /\ (forall (l : lang p) c1 c2 e1 e2 t1 t2,
           le_term l c1 c2 e1 e2 t1 t2 ->
           wf_rule l r ->
           le_term (r::l) c1 c2 e1 e2 t1 t2)
    /\ (forall (l : lang p) c1 c2,  le_ctx l c1 c2 -> wf_rule l r ->  le_ctx (r::l) c1 c2)
    /\ (forall (l : lang p) c t, wf_sort l c t -> wf_rule l r -> wf_sort (r::l) c t)
    /\ (forall (l : lang p) c s c', wf_subst l c s c' -> wf_rule l r -> wf_subst (r::l) c s c')
    /\ (forall (l : lang p) c e t,  wf_term l c e t -> wf_rule l r ->  wf_term (r::l) c e t)
    /\ (forall (l : lang p) c,  wf_ctx l c -> wf_rule l r ->  wf_ctx (r::l) c).
Proof.
  apply: mono_ind; eauto.  
  intros; apply: le_term_conv; eauto.
Qed.

Lemma le_ctx_mono {p} (l : lang p) r c1 c2
                 (wfc : le_ctx l c1 c2)
  : wf_rule l r -> le_ctx (r::l) c1 c2.
Proof.
  apply mono; auto.
Qed.
Hint Resolve le_ctx_mono.

Lemma le_sort_mono {p} (l : lang p) r c1 c2 t1 t2
                  (wfs : le_sort l c1 c2 t1 t2)
     : wf_rule l r -> le_sort (r::l) c1 c2 t1 t2.
Proof.
  apply mono; auto.
Qed.
Hint Resolve le_sort_mono.

Lemma le_subst_mono {p} (l : lang p) r c1 c2 s1 s2 c1' c2'
                   (wfsb : le_subst l c1 c2 s1 s2 c1' c2')
     : wf_rule l r -> le_subst (r::l) c1 c2 s1 s2 c1' c2'.
Proof.
  apply mono; auto.
Qed.
Hint Resolve le_subst_mono.

Lemma le_term_mono {p} (l : lang p) r c1 c2 e1 e2 t1 t2
                  (wft :  le_term l c1 c2 e1 e2 t1 t2)
  : wf_rule l r -> le_term (r::l) c1 c2 e1 e2 t1 t2.
Proof.
  apply mono; auto.
Qed.
Hint Resolve le_term_mono.

Lemma wf_sort_mono {p} (l : lang p) r c t : wf_sort l c t -> wf_rule l r -> wf_sort (r::l) c t.
Proof.
  apply mono; auto.
Qed.
Hint Resolve wf_sort_mono.
      
Lemma wf_subst_mono {p} (l : lang p) r c s c'
  : wf_subst l c s c' -> wf_rule l r -> wf_subst (r::l) c s c'.
Proof.
  apply mono; auto.
Qed.
Hint Resolve wf_subst_mono.

Lemma wf_term_mono {p} (l : lang p) r c e t
  : wf_term l c e t -> wf_rule l r -> wf_term (r::l) c e t.
Proof.
  apply mono; auto.
Qed.
Hint Resolve wf_term_mono.

Lemma wf_ctx_mono {p} (l : lang p) r c : wf_ctx l c -> wf_rule l r -> wf_ctx (r::l) c.
Proof.
  apply mono; auto.
Qed.
Hint Resolve wf_ctx_mono.

Lemma wf_rule_mono {p} (l : lang p) r r'
  : wf_rule l r' -> wf_rule l r -> wf_rule (r::l) r'.
Proof. 
  elim; auto.
Qed.
Hint Resolve wf_rule_mono.

Lemma wf_lang_prefix {p} (l1 l2 : lang p) : wf_lang (l1 ++ l2) -> wf_lang l2.
Proof.
  elim: l1; auto.
  move => r l1 IH.
  rewrite cat_cons => wfl.
  inversion wfl.
  eauto.
Qed.
Hint Immediate wf_lang_prefix.

Ltac top_inversion :=
  let H := fresh in
  move => H;
  inversion H.

Lemma wf_lang_rst {p} : forall (l : lang p) a, wf_lang (a :: l) -> wf_lang l.
Proof.
  repeat intro_term; top_inversion; apply: wf_rule_lang; eauto.
Qed.

Scheme wf_rule_lang_ind := Induction for wf_rule Sort Prop
  with wf_lang_lang_ind := Induction for wf_lang Sort Prop.

(* ==============================
   Context relation transitivity
   ============================= *)

(* manual induction scheme *)
Lemma nat2_mut_ind (Pl Pr : nat -> Prop)
  : Pl 0 ->
    Pr 0 ->
    (forall n, Pl n -> Pr (n.+1)) ->
    (forall n, Pr n -> Pl (n.+1)) ->
    (forall n, Pl n /\ Pr n).
Proof.
  move => Pl0 Pr0 Plr Prl.
  elim; auto.
  move => n; case => Pln Prn; split; auto.
Qed.

Lemma ctx_trans p (l : lang p) n
  : (forall c1 c2 c3, n = 2 * size c1 -> le_ctx l c1 c2 -> le_ctx l c2 c3 -> le_ctx l c1 c3)
    /\ (forall c1 c2 c3 v1 v2 v3,
           n = (2 * size c1).+1 ->
           le_sort l c1 c2 v1 v2 ->
           le_sort l c2 c3 v2 v3 ->
           le_sort l c1 c3 v1 v3).
Proof.
  move: n.
  apply: nat2_mut_ind.
  1,2: case; repeat intro_term; repeat top_inversion; auto.
  all: move => n IH; repeat intro_term;
    case => neq;
    repeat top_inversion; subst; eauto.
Qed.

Lemma le_ctx_trans p (l : lang p) c1 c2 c3 : le_ctx l c1 c2 -> le_ctx l c2 c3 -> le_ctx l c1 c3.
Proof.
  eapply ctx_trans; eauto.
Qed.
Hint Resolve le_ctx_trans.


Scheme ctx_refl_ind := Minimality for wf_ctx Sort Prop.

Lemma le_ctx_refl p : forall (l : lang p) (c : ctx p), wf_ctx l c -> le_ctx l c c.
Proof.
  eapply ctx_refl_ind; eauto.
Qed.
Hint Resolve le_ctx_refl.


(* note: this isn't true in general if I add a freshness condition *)
Lemma rule_in_wf {p} r : forall (l : lang p), wf_lang l -> List.In r l -> wf_rule l r.
Proof.
  case: r => [c e l | c e t l | c1 c2 t1 t2 l | c1 c2 e1 e2 t1 t2 l] wfl lin;
  constructor;
  elim: l lin wfl => //= => r l IH;
  (case => [->| linl]; top_inversion;
       do [ apply: wf_ctx_mono => //=
           | apply: wf_sort_mono => //=
           | apply: wf_term_mono => //=
           | apply: le_ctx_mono => //=
           | apply: le_sort_mono => //=
           | apply: le_term_mono => //=];
       [ by inversion H1
       | apply: IH => //=;
         apply: wf_rule_lang; eauto]).
Qed.


Scheme le_wf_ctx_ind := Minimality for le_ctx Sort Prop
  with le_wf_sort_ind := Minimality for le_sort Sort Prop
  with le_wf_subst_ind := Minimality for le_subst Sort Prop
  with le_wf_term_ind := Minimality for le_term Sort Prop.
Combined Scheme le_wf_ind from
         le_wf_sort_ind,
         le_wf_subst_ind,
         le_wf_term_ind,
         le_wf_ctx_ind.


Lemma le_wf_l {p}
  : (forall (l : lang p) c1 c2 t1 t2,
        le_sort l c1 c2 t1 t2 -> wf_sort l c1 t1)
    /\ (forall (l : lang p) c1 c2 s1 s2 c1' c2',
           le_subst l c1 c2 s1 s2 c1' c2' -> wf_subst l c1 s1 c1')
    /\ (forall (l : lang p) c1 c2 e1 e2 t1 t2,
           le_term l c1 c2 e1 e2 t1 t2 -> wf_term l c1 e1 t1)
    /\ (forall (l : lang p) c1 c2,  le_ctx l c1 c2 -> wf_ctx l c1).
Proof.
  apply: le_wf_ind; eauto; repeat intro_term;
    move => wfl /rule_in_wf rin;
     apply rin in wfl;
     by inversion wfl.
Qed.

Lemma le_wf_r {p}
  : (forall (l : lang p) c1 c2 t1 t2,
        le_sort l c1 c2 t1 t2 -> wf_sort l c2 t2)
    /\ (forall (l : lang p) c1 c2 s1 s2 c1' c2',
           le_subst l c1 c2 s1 s2 c1' c2' -> wf_subst l c2 s2 c2')
    /\ (forall (l : lang p) c1 c2 e1 e2 t1 t2,
           le_term l c1 c2 e1 e2 t1 t2 -> wf_term l c2 e2 t2)
    /\ (forall (l : lang p) c1 c2,  le_ctx l c1 c2 -> wf_ctx l c2).
Proof.
  apply: le_wf_ind; eauto; repeat intro_term;
    move => wfl /rule_in_wf rin;
     apply rin in wfl;
       by inversion wfl.
Qed.
 
Lemma le_ctx_wf_l  {p} (l : lang p) c1 c2 : le_ctx l c1 c2 -> wf_ctx l c1.
Proof.
    by eapply le_wf_l.
Qed.
Hint Immediate le_ctx_wf_l. 
Lemma le_ctx_wf_r  {p} (l : lang p) c1 c2 : le_ctx l c1 c2 -> wf_ctx l c2.
Proof.
    by eapply le_wf_r.
Qed.
Hint Immediate le_ctx_wf_r.
Lemma le_sort_wf_l  {p} (l : lang p) c1 c2 t1 t2 : le_sort l c1 c2 t1 t2 -> wf_sort l c1 t1.
Proof.
    by eapply le_wf_l.
Qed.
Hint Immediate le_sort_wf_l.
Lemma le_sort_wf_r  {p} (l : lang p) c1 c2 t1 t2 : le_sort l c1 c2 t1 t2 -> wf_sort l c2 t2.
Proof.
    by eapply le_wf_r.
Qed.
Hint Immediate le_sort_wf_r.
Lemma le_term_wf_l  {p} (l : lang p) c1 c2 e1 e2 t1 t2
  : le_term l c1 c2 e1 e2 t1 t2 -> wf_term l c1 e1 t1.
Proof.
    by eapply le_wf_l.
Qed.
Hint Immediate le_term_wf_l.
Lemma le_term_wf_r  {p} (l : lang p) c1 c2 e1 e2 t1 t2
  : le_term l c1 c2 e1 e2 t1 t2 -> wf_term l c2 e2 t2.
Proof.
    by eapply le_wf_r.
Qed.
Hint Immediate le_term_wf_r.
Lemma le_subst_wf_l  {p} (l : lang p) c1 c2 s1 s2 c1' c2'
  : le_subst l c1 c2 s1 s2 c1' c2' -> wf_subst l c1 s1 c1'.
Proof.
    by eapply le_wf_l.
Qed.
Hint Immediate le_subst_wf_l.
Lemma le_subst_wf_r  {p} (l : lang p) c1 c2 s1 s2 c1' c2'
  : le_subst l c1 c2 s1 s2 c1' c2' -> wf_subst l c2 s2 c2'.
Proof.
    by eapply le_wf_r.
Qed.
Hint Immediate le_subst_wf_r.

(* TODO: finish the proof
Lemma wf_to_ctx {p}
  : (forall (l : lang p) c1 c2 t1 t2,
        le_sort l c1 c2 t1 t2 -> le_ctx l c1 c2)
    /\ (forall (l : lang p) c1 c2 s1 s2 c1' c2',
           le_subst l c1 c2 s1 s2 c1' c2' -> le_ctx l c1 c2)
    /\ (forall (l : lang p) c1 c2 e1 e2 t1 t2,
           le_term l c1 c2 e1 e2 t1 t2 -> le_ctx l c1 c2)
    /\ (forall (l : lang p) c1 c2,  le_ctx l c1 c2 -> le_ctx l c1 c2)
    /\ (forall (l : lang p) c1 c2 v1 v2,
           le_ctx_var l c1 c2 v1 v2 -> le_ctx l c1 c2)
    /\ (forall (l : lang p) c t, wf_sort l c t -> wf_ctx l c)
    /\ (forall (l : lang p) c s c', wf_subst l c s c' -> wf_ctx l c)
    /\ (forall (l : lang p) c e t,  wf_term l c e t -> wf_ctx l c)
    /\ (forall (l : lang p) c,  wf_ctx l c -> wf_ctx l c)
    /\ (forall (l : lang p) c v,  wf_ctx_var l c v -> wf_ctx l c).
Proof.
  apply: mono_ind;
    eauto;
    repeat intro_term;
    move => wfl /rule_in_wf => riwf;
    apply riwf in wfl;
    try by inversion wfl.
  - inversion wfl.
    give_up. (*TODO: need IH for sort here *)
  - apply: le_ctx_refl.
      by inversion wfl.
Fail Qed.
*)

(* constructor conversion lemmas *)

Ltac rewrite_constr_eqs :=
  repeat match goal with
  | [ |- _ = _ -> _] => move => ->
  | _ => intro
  end.

(* TODO: useful or no?
Lemma wf_ctx_iff_variant {p} (l : lang p) c : wf_ctx l c <-> wf_ctx_ l c.
Proof.
  split;case; rewrite_constr_eqs; by eauto.
Qed.
Coercion wf_ctx_from_variant p (l : lang p) c := iffRL (wf_ctx_iff_variant l c).

Lemma wf_ctx_var_iff_variant {p} (l : lang p) c v : wf_ctx_var l c v <-> wf_ctx_var_ l c v.
Proof.
  split;case; rewrite_constr_eqs; by eauto.
Qed.
Coercion wf_ctx_var_from_variant p (l : lang p) c v := iffRL (wf_ctx_var_iff_variant l c v).

Lemma wf_sort_iff_variant {p} (l : lang p) c t : wf_sort l c t <-> wf_sort_ l c t.
Proof.
  split;case; rewrite_constr_eqs; by eauto.
Qed.
Coercion wf_sort_from_variant p (l : lang p) c t := iffRL (wf_sort_iff_variant l c t).

Lemma wf_subst_iff_variant {p} (l : lang p) c s c' : wf_subst l c s c' <-> wf_subst_ l c s c'.
Proof.
  split;case; rewrite_constr_eqs; by eauto.
Qed.
Coercion wf_subst_from_variant p (l : lang p) c s c' := iffRL (wf_subst_iff_variant l c s c').

(* TODO: why does this one fail?
Lemma wf_term_iff_variant {p} (l : lang p) c e t : wf_term l c e t <-> wf_term_ l c e t.
Proof.
  split;case; rewrite_constr_eqs; eauto.
Fail Qed.
Coercion wf_term_from_variant p (l : lang p) c e t := iffRL (wf_term_iff_variant l c e t).
*)

Lemma le_ctx_iff_variant {p} (l : lang p) c1 c2 : le_ctx l c1 c2 <-> le_ctx_ l c1 c2.
Proof.
  split;case; rewrite_constr_eqs; eauto;
    (* TODO: why doesn't eauto handle this?*)
    by constructor.    
Qed.
Coercion le_ctx_from_variant p (l : lang p) c1 c2 := iffRL (le_ctx_iff_variant l c1 c2).

Lemma le_ctx_var_iff_variant {p} (l : lang p) c1 c2 v1 v2
  : le_ctx_var l c1 c2 v1 v2 <-> le_ctx_var_ l c1 c2 v1 v2.
Proof.
  split;case; rewrite_constr_eqs;  eauto.
Qed.
Coercion e_ctx_var_from_variant p (l : lang p) c1 c2 v1 v2 :=
  iffRL (le_ctx_var_iff_variant l c1 c2 v1 v2).

Lemma le_sort_iff_variant {p} (l : lang p) c1 c2 t1 t2
  : le_sort l c1 c2 t1 t2 <-> le_sort_ l c1 c2 t1 t2.
Proof.
  split;case; rewrite_constr_eqs; by eauto.
Qed.
Coercion le_sort_from_variant p (l : lang p) c1 c2 t1 t2 :=
  iffRL (le_sort_iff_variant l c1 c2 t1 t2).

Lemma le_subst_iff_variant {p} (l : lang p) c1 c2 s1 s2 c1' c2'
  : le_subst l c1 c2 s1 s2 c1' c2' <-> le_subst_ l c1 c2 s1 s2 c1' c2'.
Proof.
  split;case; rewrite_constr_eqs; by eauto.
Qed.
Coercion le_subst_from_variant p (l : lang p) c1 c2 s1 s2 c1' c2' :=
  iffRL (le_subst_iff_variant l c1 c2 s1 s2 c1' c2').

Lemma le_term_iff_variant {p} (l : lang p) c1 c2 e1 e2 t1 t2
  : le_subst l c1 c2 e1 e2 t1 t2 <-> le_subst_ l c1 c2 e1 e2 t1 t2.
Proof.
  split;case; rewrite_constr_eqs; by eauto.
Qed.
Coercion le_term_from_variant p (l : lang p) c1 c2 e1 e2 t1 t2 :=
  iffRL (le_term_iff_variant l c1 c2 e1 e2 t1 t2).
*)

Lemma wf_shift_subst {p} (l : lang p) c c'
  : wf_ctx l (c' ++ c) -> wf_subst l (c' ++ c) (shift_subst (size c) (size c')) c.
Proof.
  elim: c c'.
  - move => c';
    rewrite cats0;
      simpl;
      auto.
  - intros.
    simpl.
    constructor;
    move: H0;
      change (a :: l0) with ([::a]++ l0);
      suff: size (c'++[::a]) = (size c').+1;
      try (by elim: c'; simpl; auto);
      move <-.
    + rewrite catA;
        by apply H.
    + move=> wfc.
      rewrite extract_var_shift.
      erewrite <-shift_subst_shift.
      instantiate(1:=1).
      (*TODO: strengthen? e.g. n <= size c'?*)
      eapply wf_term_subst.
      change (size c') with (0+(size c')).
      erewrite <-lookup_in_shift_subst; eauto.
      eapply wf_term_subst.
 
    
    
Lemma wf_sort_weaken {p} (l : lang p) c s
  : wf_sort l c s -> forall v, wf_ctx_var l c v -> wf_sort l (v::c) s^!1.
Proof.
  intros.
  suff: ws_exp (size c) s => [wse|].
  erewrite <-shift_subst_shift; eauto.
  apply: wf_sort_subst; eauto.
  give_up. (* need to prove that shift_substs are well-typed *)
  give_up. (* need to prove that well-typed terms are well-scoped*)
  
