
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
  repeat match goal with
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
Lemma wf_ctx_lang (l : lang) c (wf : wf_ctx l c) : wf_lang l
with wf_sort_lang (l : lang) c t (wf : wf_sort l c t) : wf_lang l
with wf_term_lang (l : lang) c e t
      (wf : wf_term l c e t) : wf_lang l
with wf_subst_lang (l : lang) c s c'
           (wf : wf_subst l c s c') : wf_lang l.
  all: case: wf => //=;
       intros;
       first [apply: wf_subst_lang; eassumption
                 | apply: wf_term_lang; eassumption].
Qed.
Hint Immediate wf_ctx_lang.
Hint Immediate wf_sort_lang.
Hint Immediate wf_term_lang.
Hint Immediate wf_subst_lang.

Lemma wf_rule_lang (l : lang) r
      (wf : wf_rule l r) : wf_lang l.
Proof.
  case: wf => //=; eauto.
Qed.
Hint Immediate wf_rule_lang.


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

Ltac expand_rule_shift :=
  match goal with
  | |- context [ {| ?c ::%! 1 |- sort}] =>
    change ({| ?c ::%! 1 |- sort})
      with ({| c |- sort})%%!1
  | |- context [ {| ?c ::%! 1 |- ?t %! 1}] =>
    change ({| ?c ::%! 1 |- ?t %! 1})
      with ({| c |- t})%%!1
  | |- context [ {<?c1 ::%! 1 <# ?c2 ::%! 1 |- ?t1 %! 1 <# ?t2 %! 1}] =>
    change ({<?c1 ::%! 1 <# ?c2 ::%! 1 |- ?t1 %! 1 <# ?t2 %! 1})
      with ({<c1 <# c2 |- t1 <# t2})%%!1
  | |- context [ {<?c1 ::%! 1 <# ?c2 ::%! 1 |- ?e1%!1 <# ?e2%!1 .: ?t1 %! 1 <# ?t2 %! 1}] =>
    change ({<?c1 ::%! 1 <# ?c2 ::%! 1 |- ?e1%!1 <# ?e2%!1 .: ?t1 %! 1 <# ?t2 %! 1})
      with ({<c1 <# c2 |- e1 <# e2 .: t1 <# t2})%%!1
  end.

Lemma mono r
  : (forall (l : lang) c1 c2 t1 t2,
        le_sort l c1 c2 t1 t2 -> wf_rule l r ->
        le_sort (r::l) c1::%!1 c2::%!1 t1%!1 t2%!1)
    /\ (forall (l : lang) c1 c2 s1 s2 c1' c2',
           le_subst l c1 c2 s1 s2 c1' c2' ->
           wf_rule l r ->
           le_subst (r::l) c1::%!1 c2::%!1 s1::%!1 s2::%!1 c1'::%!1 c2'::%!1)
    /\ (forall (l : lang) c1 c2 e1 e2 t1 t2,
           le_term l c1 c2 e1 e2 t1 t2 ->
           wf_rule l r ->
           le_term (r::l) c1::%!1 c2::%!1 e1%!1 e2%!1 t1%!1 t2%!1)
    /\ (forall (l : lang) c1 c2,
           le_ctx l c1 c2 ->
           wf_rule l r ->
           le_ctx (r::l) c1::%!1 c2::%!1)
    /\ (forall (l : lang) c t,
           wf_sort l c t -> wf_rule l r -> wf_sort (r::l) c::%!1 t%!1)
    /\ (forall (l : lang) c s c',
           wf_subst l c s c' -> wf_rule l r -> wf_subst (r::l) c::%!1 s::%!1 c'::%!1)
    /\ (forall (l : lang) c e t,
           wf_term l c e t -> wf_rule l r ->  wf_term (r::l) c::%!1 e%!1 t%!1)
    /\ (forall (l : lang) c,
           wf_ctx l c -> wf_rule l r ->  wf_ctx (r::l) c::%!1).
Proof.
  apply: mono_ind; intros; eauto.
  all: try solve[ constructor; try expand_rule_shift; move: rule_in_mono; eauto
                | rewrite !constr_shift_subst_comm; eauto
                | simpl; constructor; eauto; rewrite -!constr_shift_subst_comm; auto
                | apply: le_term_conv; eauto].
  simpl; econstructor; eauto;
  unfold is_nth; simpl;
  change 1 with (0 + 1) at 1;
  expand_rule_shift;
    by apply: unshift_is_nth_cons.

  rewrite constr_shift_subst_comm.
  simpl; eapply wf_term_by; eauto.
  unfold is_nth; simpl.
  change 1 with (0 + 1) at 1;
  expand_rule_shift;
    by apply: unshift_is_nth_cons.
Qed.

Lemma mono_n l'
  : (forall (l : lang) c1 c2 t1 t2,
        le_sort l c1 c2 t1 t2 -> wf_lang (l'++l) ->
        le_sort (l'++ l) c1::%!(size l') c2::%!(size l') t1%!(size l') t2%!(size l'))
    /\ (forall (l : lang) c1 c2 s1 s2 c1' c2',
           le_subst l c1 c2 s1 s2 c1' c2' ->
           wf_lang (l' ++ l) ->
           le_subst (l'++ l)
                    c1::%!(size l') c2::%!(size l')
                    s1::%!(size l') s2::%!(size l')
                    c1'::%!(size l') c2'::%!(size l'))
    /\ (forall (l : lang) c1 c2 e1 e2 t1 t2,
           le_term l c1 c2 e1 e2 t1 t2 ->
           wf_lang (l' ++ l) ->
           le_term (l' ++ l) 
                   c1::%!(size l') c2::%!(size l')
                   e1%!(size l') e2%!(size l')
                   t1%!(size l') t2%!(size l'))
    /\ (forall (l : lang) c1 c2,
           le_ctx l c1 c2 ->
           wf_lang (l' ++ l) ->
           le_ctx (l' ++ l) c1::%!(size l') c2::%!(size l'))
    /\ (forall (l : lang) c t,
           wf_sort l c t -> wf_lang (l' ++ l) -> wf_sort (l' ++ l) c::%!(size l') t%!(size l'))
    /\ (forall (l : lang) c s c',
           wf_subst l c s c' ->
           wf_lang (l' ++ l) ->
           wf_subst (l'++ l) c::%!(size l') s::%!(size l') c'::%!(size l'))
    /\ (forall (l : lang) c e t,
           wf_term l c e t ->
           wf_lang (l' ++ l) ->
           wf_term (l' ++ l) c::%!(size l') e%!(size l') t%!(size l'))
    /\ (forall (l : lang) c,
           wf_ctx l c -> wf_lang (l' ++ l) -> wf_ctx (l'++l) c::%!(size l')).
Proof.
  elim: l'; simpl;
    try by repeat match goal with |- _/\_ => split end;
    intros; rewrite ?constr_shift0 ?map_constr_shift0.
  intros.
  repeat match goal with |- _/\_ => split end;
    intros.
  all: by change (size l).+1 with (1 + size l);
    rewrite addnC -?rule_constr_shift_shift -?map_constr_shift_shift -?constr_shift_shift;
    eapply mono; [eapply H|];
    inversion H1; eauto.
Qed.

(*
Lemma le_ctx_mono (l : lang) r c1 c2
                 (wfc : le_ctx l c1 c2)
  : wf_rule l r -> le_ctx (r::l) c1::%!1 c2::%!1.
Proof.
  apply mono; auto.
Qed.
(*Hint Resolve le_ctx_mono. TODO: use DBs *)

Lemma le_sort_mono l r c1 c2 t1 t2
                  (wfs : le_sort l c1 c2 t1 t2)
     : wf_rule l r -> le_sort (r::l) c1::%!1 c2::%!1 t1%!1 t2%!1.
Proof.
  apply mono; auto.
Qed.

Lemma le_subst_mono l r c1 c2 s1 s2 c1' c2'
                   (wfsb : le_subst l c1 c2 s1 s2 c1' c2')
     : wf_rule l r -> le_subst (r::l) c1::%!1 c2::%!1 s1::%!1 s2::%!1 c1'::%!1 c2'::%!1.
Proof.
  apply mono; auto.
Qed.

Lemma le_term_mono l r c1 c2 e1 e2 t1 t2
                  (wft :  le_term l c1 c2 e1 e2 t1 t2)
  : wf_rule l r -> le_term (r::l) c1::%!1 c2::%!1 e1%!1 e2%!1 t1%!1 t2%!1.
Proof.
  apply mono; auto.
Qed.

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
*)

Lemma wf_lang_prefix l1 l2 : wf_lang (l1 ++ l2) -> wf_lang l2.
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

Lemma wf_lang_rst : forall l a, wf_lang (a :: l) -> wf_lang l.
Proof.
  intro_to wf_lang; top_inversion; eauto.
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

Lemma ctx_trans' l n
  : (forall c1 c2 c3, n = size c1 * 2 -> le_ctx l c1 c2 -> le_ctx l c2 c3 -> le_ctx l c1 c3)
    /\ (forall c1 c2 c3 v1 v2 v3,
           n = (size c1 * 2).+1 ->
           le_sort l c1 c2 v1 v2 ->
           le_sort l c2 c3 v2 v3 ->
           le_sort l c1 c3 v1 v3).
Proof.
  move: n.
  apply: nat2_mut_ind.
  1,2: case; repeat intro_term; repeat top_inversion; auto.
  - intro_to (@eq nat); case; eauto.
  - intro_to seq.
    case => // a1 c1.
    simpl.
    case => //; [intro_to le_ctx; top_inversion|]; move => a2 c2.
    case => //; [ move => _ _; top_inversion|]; move => a3 c3.
    change ((size c1).+1 * 2) with (size c1 * 2).+2.
    case => neq.
    repeat top_inversion; eauto.
Qed.

Lemma le_ctx_trans l c1 c2 c3 : le_ctx l c1 c2 -> le_ctx l c2 c3 -> le_ctx l c1 c3.
Proof.
  eapply ctx_trans'; eauto.
Qed.

Scheme ctx_refl_ind := Minimality for wf_ctx Sort Prop.

Lemma le_ctx_refl : forall l c, wf_ctx l c -> le_ctx l c c.
Proof.
  eapply ctx_refl_ind; eauto.
Qed.
Hint Resolve le_ctx_refl.


Lemma is_nth_list_split m r l n
  : shifted_is_nth m r l n ->
    exists l1 r' l2, l = l1 ++ (r':: l2) /\ r = r'%%!(m + n) /\ n = (size l1).
Proof.
  elim: n l m.
  - case; simpl;
      intro_to is_true;
      [intro_to is_true; top_inversion|].
    rewrite addn0.
    move /eqP; intros;
    exists [::]; simpl; eauto.
  - intro_to seq.
    case; simpl; [intro_to is_true; top_inversion|].
    intros.
    rewrite addnS. 
    change (m + n).+1 with (m.+1 + n).
    case: (H l m.+1 H0) => l1 [r' [l2[[]]]] -> [] -> neq.
    exists (a::l1).
    exists r'.
    exists l2.
    rewrite {3}neq.
    eauto.
Qed.

(*
Lemma rule_in_wf r l : wf_lang l -> forall n, is_nth r l n -> wf_rule l r.
Proof.
  case: r => [c e | c e t | c1 c2 t1 t2 | c1 c2 e1 e2 t1 t2] n.
  - constructor.
    move: H => /is_nth_list_split.
    change (0+n) with n.
    case => l1 [r'[l2 []]] leq [req neq].
    subst.
    case: r' e req; intro_to (@eq rule); simpl; try by top_inversion.
    case => ->.
    elim: l1 e; simpl.
    + rewrite map_constr_shift0.
      give_up.
    +intros.
  
  
  Lemma is_nth_list_split : is_nth r l n -> exists l1 r' l2, l = l1 ++ [:: r'] ++ l2 /\ r'%%!n = r.
  eapply mono_n.
  elim: l lin wfl => //= => r l IH.
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
      (*TODO: is there a place I'm missing shifts in the defs?*)
      (* posible since Jon Sterling doesn't use debruijn *)
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
*)
  
