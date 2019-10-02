
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
  | [|- seq (ctx_var _) -> _] => intro
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
Hint Immediate wf_ctx_lang.
Hint Immediate wf_ctx_var_lang.
Hint Immediate wf_sort_lang.

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
Hint Immediate wf_term_lang.

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
  with le_ctx_var_mono_ind := Minimality for le_ctx_var Sort Prop
  with wf_sort_mono_ind := Minimality for wf_sort Sort Prop
  with wf_subst_mono_ind := Minimality for wf_subst Sort Prop
  with wf_term_mono_ind := Minimality for wf_term Sort Prop
  with wf_ctx_mono_ind := Minimality for wf_ctx Sort Prop
  with wf_ctx_var_mono_ind := Minimality for wf_ctx_var Sort Prop.

Combined Scheme mono_ind from
         le_sort_mono_ind,
         le_subst_mono_ind,
         le_term_mono_ind,
         le_ctx_mono_ind,
         le_ctx_var_mono_ind,
         wf_sort_mono_ind,
         wf_subst_mono_ind,
         wf_term_mono_ind,
         wf_ctx_mono_ind,
         wf_ctx_var_mono_ind.

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
    /\ (forall (l : lang p) c1 c2 v1 v2,
           le_ctx_var l c1 c2 v1 v2 -> wf_rule l r ->  le_ctx_var (r::l) c1 c2 v1 v2)
    /\ (forall (l : lang p) c t, wf_sort l c t -> wf_rule l r -> wf_sort (r::l) c t)
    /\ (forall (l : lang p) c s c', wf_subst l c s c' -> wf_rule l r -> wf_subst (r::l) c s c')
    /\ (forall (l : lang p) c e t,  wf_term l c e t -> wf_rule l r ->  wf_term (r::l) c e t)
    /\ (forall (l : lang p) c,  wf_ctx l c -> wf_rule l r ->  wf_ctx (r::l) c)
    /\ (forall (l : lang p) c v,  wf_ctx_var l c v -> wf_rule l r ->  wf_ctx_var (r::l) c v).
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
  
Lemma le_ctx_var_mono {p} (l : lang p) r c1 c2 v1 v2
                     (wfv : le_ctx_var l c1 c2 v1 v2)
     : wf_rule l r -> le_ctx_var (r::l) c1 c2 v1 v2.
Proof.
  apply mono; auto.
Qed.
Hint Resolve le_ctx_var_mono.

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

Lemma wf_ctx_var_mono {p} (l : lang p) r c v
  : wf_ctx_var l c v -> wf_rule l r -> wf_ctx_var (r::l) c v.
Proof.
  apply mono; auto.
Qed.
Hint Resolve wf_ctx_var_mono.

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
Check wf_lang_lang_ind.


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
           le_ctx_var l c1 c2 v1 v2 ->
           le_ctx_var l c2 c3 v2 v3 ->
           le_ctx_var l c1 c3 v1 v3).
Proof.
  move: n.
  apply: nat2_mut_ind.
  - case; repeat intro_term; repeat top_inversion; auto.
  - case; repeat intro_term; repeat top_inversion; auto.
  - move => n IH; repeat intro_term;
    case;
    repeat top_inversion;
    constructor;
    [ apply: IH
    | apply: le_sort_trans]; eauto.
  - move => n IH; repeat intro_term.
    move => neq.
    repeat top_inversion; constructor; auto.
    apply: IH; eauto.
    move: neq.
    rewrite -H2 !mul2n doubleS.
    auto.
Qed.

Lemma le_ctx_trans p (l : lang p) c1 c2 c3 : le_ctx l c1 c2 -> le_ctx l c2 c3 -> le_ctx l c1 c3.
Proof.
  eapply ctx_trans; eauto.
Qed.
Hint Resolve le_ctx_trans.

Lemma le_ctx_var_trans p (l : lang p) c1 c2 c3 v1 v2 v3 :
  le_ctx_var l c1 c2 v1 v2 -> le_ctx_var l c2 c3 v2 v3 -> le_ctx_var l c1 c3 v1 v3.
Proof.
  eapply ctx_trans; eauto.
Qed.
Hint Resolve le_ctx_var_trans.

Scheme wf_ctx_var_refl_ind := Minimality for wf_ctx_var Sort Prop
  with wf_ctx_refl_ind := Minimality for wf_ctx Sort Prop.
Combined Scheme ctx_refl_ind from wf_ctx_refl_ind, wf_ctx_var_refl_ind.

Lemma le_refl p 
  : (forall (l : lang p) (c : ctx p), wf_ctx l c -> le_ctx l c c)
    /\ (forall (l : lang p) c v, wf_ctx_var l c v -> le_ctx_var l c c v v).
Proof.
  eapply ctx_refl_ind; eauto.
Qed.

Lemma le_ctx_refl p (l : lang p) c : wf_ctx l c -> le_ctx l c c.
Proof.
  eapply le_refl.
Qed.
Hint Resolve le_ctx_refl.

Lemma le_ctx_var_refl p (l : lang p) c v : wf_ctx_var l c v -> le_ctx_var l c c v v.
Proof.
  eapply le_refl.
Qed.
Hint Resolve le_ctx_var_refl.


(* note: this isn't true in general if I add a freshness condition *)
Lemma rule_in_wf {p} : forall (l : lang p), wf_lang l -> forall r, List.In r l -> wf_rule l r.
Proof.
  apply: (@wf_lang_lang_ind p (fun l r' wfr' => forall r, List.In r l -> wf_rule l r)).
  case.
  repeat do [move => lin; by inversion lin | intro].
  move => r l c _ wfc r'.
  case => req.
  move: req wfc => -> wfc.
  apply: wf_rule_mono.
  apply wf_ctx_lang in wfc.
  by inversion wfc.
  apply wf_ctx_lang in wfc.
  by inversion wfc.
  
  
  move => l r wfr huh r'.
  case.
  - move => req.
    move: req wfr huh => -> wfr huh.
      by apply: wf_rule_mono.
  - move => l c t wfc.
    
    eauto.
    eauto. done.
    apply: wf_sort_rule.
  
  apply: wf_lang_ind'.
  - move => l c t wfc.
    


  induction l.
  - move => _ r lin; exfalso; auto using List.in_nil.
  - move => wfl r lin.
    inversion lin; [rewrite -H; auto|].
    
    Focus 2.
  - apply: wf_rule_mono.
    apply: IHl; eauto using wf_lang_rst.
    apply: IHl; eauto using wf_lang_rst.

    destruct wfl; auto.
    + exfalso; auto using List.in_nil.
    + 

    apply: wf_lang_rst. move: (IHl (wf_lang_rst wfl) a).
    move => impl.
    

    destruct wfl.
    + auto.

  elim; auto.
  - move => r lin; exfalso; auto using List.in_nil.
  - move => l' r wfr r' lin.
    inversion lin; [rewrite -H; auto|].
    apply: wf_rule_mono; auto.
    


    case => [<-|]; auto.
    eauto.
    
  move => l' r' wfr' lin.
  inversion lin; [rewrite -H; auto|].
  auto.
  apply: wf_rule_mono; auto.
  case => [<-|]; auto.
  
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
  - move => l' c1' c2' t1' t2' wfl lin.
    apply List.in_split in lin;
      case: lin => ll;
      case => lr l'eq.
    rewrite l'eq in wfl.
    pose wfl' := (wf_lang_prefix wfl).
    inversion wfl'.
    inversion H0.
    rewrite l'eq.
    move: l'eq wfl' => _ _.
    elim: ll wfl H8; simpl; auto.
    move => r' ll IH wfl' wfs.
    apply: wf_sort_mono; auto.
    apply: IH; auto.
    inversion wfl'.
    apply: wf_rule_lang; eauto.
    inversion wfl'; auto.
  - move => l' c1' c2' s1 s2 c1'' c2'' t1' t2' lesb les.
    apply: le_sort_wf_l.
    
    Check List.in_split.
  Search _ (List.In).
  (* depends on monotonicity *)
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
