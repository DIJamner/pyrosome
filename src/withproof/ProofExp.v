
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From excomp Require Import Utils.

Inductive lepf : Set :=
(* because of refl and trans, it is easier to separate by and subst *)
| lepf_by : nat -> lepf
(* we prove relatedness of substitutions by pointwise proofs *)
| lepf_subst : lepf -> seq lepf -> lepf 
| lepf_refl : lepf
| lepf_trans : lepf -> lepf -> lepf
(* applies a sort relation to the type of a term relation *)
| lepf_conv : lepf -> lepf -> lepf.
(*TODO: need conv for pfs?*)
 
Unset Elimination Schemes.
Inductive exp : Set :=
(* variable deBruijn level *)
| var : nat -> exp
(* Rule deBruijn level, list of subterms*)
| con : nat -> seq exp -> exp
(* sort rewrite *)
| conv : lepf -> exp -> exp.
Set Elimination Schemes.
Print List.Forall.
Fixpoint exp_ind
         (P : exp -> Prop)
         (IHV : forall n, P(var n))
         (IHC : forall n l,
             List.Forall P l ->
             P (con n l))
         (IHCV : forall pf e,
             P e -> P (conv pf e))
         (e : exp) { struct e} : P e :=
  match e with
  | var n => IHV n
  | con n l =>
    let fix loop l :=
        match l return List.Forall P l with
        | [::] => List.Forall_nil _
        | e' :: l' => List.Forall_cons _ (exp_ind IHV IHC IHCV e') (loop l')
        end in
    IHC n l (loop l)
  | conv pf e =>
    IHCV pf e (exp_ind IHV IHC IHCV e)
  end.

Fixpoint exp_rect
         (P : exp -> Type)
         (IHV : forall n, P(var n))
         (IHC : forall n l,
             List.fold_right (fun t : exp => prod (P t)) unit l ->
             P (con n l))
         (IHCV : forall pf e,
             P e -> P (conv pf e))
         (e : exp) { struct e} : P e :=
  match e with
  | var n => IHV n
  | con n l =>
    let fix loop l :=
        match l return List.fold_right (fun t => prod (P t)) unit l with
        | [::] => tt
        | e' :: l' => (exp_rect IHV IHC IHCV e', loop l')
        end in
    IHC n l (loop l)
  | conv pf e =>
    IHCV pf e (exp_rect IHV IHC IHCV e)
  end.

Definition exp_rec := 
[eta exp_rect]
     : forall P : exp -> Set,
       (forall n : nat, P (var n)) ->
       (forall n l,
             List.fold_right (fun t : exp => prod (P t)) unit l ->
             P (con n l))->
       (forall pf e,
             P e -> P (conv pf e)) -> forall e : exp, P e.

Notation "[ n | ]" := (con n [::]).
Notation "[ n | e ]" := (con n [:: e]).
Notation "[ n | e ; .. ; e' ]" := (con n (cons e .. (cons e' [::]) ..)).

(* TODO: what's the right thing to do? need intuition from denotations, compilers
Variant constr (T : Set) : Set :=
| ccon : nat -> seq T -> constr T.

Notation "[{ T } n | ]" := (ccon T n [::]).
Notation "[{ T } n | e ]" := (ccon T n [:: e]).
Notation "[{ T } n | e ; .. ; e' ]" := (ccon T n (cons e .. (cons e' [::]) ..)).

Definition Alg T := constr T -> T.

Fixpoint alg_fn (a : Alg) (e : exp) : exp :=
  match e with
  | var n => var n
  | con n l => a (ccon n (map (alg_fn a) l))
  end.    

Definition id_alg : Alg := fun ce =>
  match ce with
  | ccon n l => con n l
  end.
*)

(* TODO: uniform inheritance condition? this feels like it would be nice to have
Coercion id_alg : constr >-> exp. *)

Definition ctx := list exp.


Definition subst := seq exp.

Definition var_lookup (c : subst) (n : nat) : exp :=
  nth_level (var n) c n.
Global Transparent var_lookup.

Fixpoint exp_var_map (f : nat -> exp) (e : exp) : exp :=
  match e with
  | var n => f n
  | con n l => con n (map (exp_var_map f) l)
  | conv pf e' => conv pf (exp_var_map f e')
  end.

Definition exp_subst (s : subst) e : exp :=
  exp_var_map (var_lookup s) e.

Notation "e [/ s /]" := (exp_subst s e) (at level 7, left associativity).

Definition subst_cmp s1 s2 : subst := map (exp_subst s2) s1.


Lemma con_subst_cmp n s s0 : (con n s0)[/s/] = con n (subst_cmp s0 s).
Proof using .
  unfold exp_subst.
  simpl.
  f_equal.
Qed.


Definition exp_shift (m : nat) e : exp :=
  exp_var_map (fun n => var (m + n)) e.

Notation "e ^! n" := (exp_shift n e) (at level 7, left associativity).
Notation "s ^!! n" := (map (exp_shift n) s) (at level 7, left associativity).

Fixpoint shift_subst (sz start : nat) : subst :=
  match sz with
  | 0 => [::]
  | sz'.+1 => (var start)::(shift_subst sz' (start.+1))
  end.

(*TODO: this is in the library. Why can't I find it? *)
Lemma sub_0_r : forall n, n - 0 = n.
Proof using .
  elim; done.
Qed.  

Lemma lookup_ge : forall c n, ~n < size c -> var_lookup c n = var n.
Proof using .
  intros; unfold var_lookup; unfold nth_level.
  case nlt: (n < size c) => //=.
Qed.

(*TODO*)
(* Well-scoped languages
   a presupposition of well-formed languages
   Written as functions that decide the properties
   determines that variables (but not constructor symbols) are well-scoped
 *)

Fixpoint ws_exp csz (e : exp) : bool :=
  match e with
  | var n => n < csz
  | con _ v => List.fold_right (fun e f => (ws_exp csz e) && f) true v
  | conv _ e => ws_exp csz e
  end.

Fixpoint ws_ctx (c : ctx) : bool :=
  match c with
  | [::] => true
  | t :: c' => ws_ctx c' && ws_exp (size c') t
  end.


(* replaces m variables with terms with n free vars*)
Definition ws_subst n : subst -> bool :=
  List.fold_right (fun e b => ws_exp n e && b) true.


Lemma unandb : forall (a b : bool) (C : Prop), (a -> b -> C) <-> (a && b -> C).
Proof using .
  move => a b C; split.
  - move => CF ab.
    apply andb_prop in ab.
    case: ab.
    done.
  - move => CF aa bb.
    apply CF.
    rewrite andb_true_intro //=.
Qed.

Lemma ws_nth : forall n (s : subst) e n',
    ws_subst n s -> ws_exp n e -> ws_exp n (nth e s n').
Proof using .
  move => n ; elim.
  - move => e; elim; [done|].
    move => n' IH //=.
  - move => x l IH e.
    elim => [| n' _].
    + rewrite /ws_subst //=.
      repeat case /andb_prop.
      done.
    + rewrite /ws_subst //=.
      repeat case /andb_prop.
      move => _ lf wse.
      apply: IH.
      rewrite /ws_subst //=. 
      done.
Qed.

Lemma ws_empty : forall n, ws_subst n [::].
Proof using .
  move => n.
  rewrite /ws_subst //=.
Qed.

Lemma sub_n_n n : n - n = 0.
Proof using .
  elim: n => //=.
Qed.

Lemma ltn_lte a b : a < b -> a <= b.
Proof using .
  elim: b a; simpl; auto.
Qed.  

Lemma sub_flip a b c : a < b -> c = b - a.+1 -> a = b -c.+1.
Proof using .
  move => alt ->.
  clear c.
  rewrite subnSK //.
  rewrite subKn //.
  auto using ltn_lte.
Qed.


Lemma level_ind sz m (R: nat -> nat -> Prop)
  : (forall n, n < sz -> R n (sz - n.+1)) -> m < sz -> R (sz - m.+1) m.
Proof using .
  intros.
  remember (sz - m.+1) as n.
  move: (sub_flip H0 Heqn) ->.
  apply: H.
  rewrite Heqn; clear Heqn.
  case: sz H0 => //= sz.
  rewrite !subSS.
  intros.
  apply: sub_ord_proof.
Qed.


(* TODO: use above principle *)
Lemma ws_lookup : forall n (s : subst) (n' : nat),
    ws_subst n s -> n' < size s -> ws_exp n (var_lookup s n').
Proof using .  
  move => n.
  unfold var_lookup;
    unfold nth_level.
  intros.
  pose p := H0; move: p; case: (n'< size s) => //= _.
  remember (size s - n'.+1) as y.
  suff: n' = size s - y.+1.
  move => n'eq.
  suff: y < size s.
  {
    move: n'eq => -> ylt.
    clear Heqy H0 n'.
    elim: y s ylt H;
      intros until s;
      case: s => //= e s nlt /andP [wse wss] //=.
    rewrite subSS.
    suff: n0 < size s; auto.
  }
  move: H0 Heqy n'eq.
  generalize (size s) as z.
  case => //= n0.
  rewrite !subSS.
  intros.
  rewrite Heqy.
  apply: sub_ord_proof.
  auto using sub_flip.
Qed.


Theorem subst_preserves_ws
  : forall e (s : subst) (csz : nat),
    ws_exp (size s) e ->
    ws_subst csz s ->
    ws_exp csz (exp_subst s e).
Proof using .
  move => e s c wse.
  move => wss.
  pose (wss' := wss).
  move: wss'.
  rewrite /ws_subst.
  move => elem_ws.
  elim: e wse => //= => n.
  - apply: ws_lookup => //=;
    move: size_eq => /eqP -> //=.
  - elim => //= x l' IHA IHB.
    case /andP => xexp rexp.
    inversion IHB.
    apply /andP. split; [auto|].
    move: IHA -> => //=.
Qed.


Lemma map_ext {B C : Type} (f g : B -> C) (l : seq B)
  : (forall e, f e = g e) -> map f l = map g l.
Proof.
  move => ext.
  elim: l; try done.
  move => e1 l' IH.
  simpl.
    by rewrite ext IH.
Qed.

Lemma map_ext' {B C : Type} (f g : B -> C) (v : seq B)
  : forall (P : B -> bool),
    (forall e, P e -> f e = g e) ->
    List.fold_right (fun e => [eta andb (P e)]) true v ->
    map f v = map g v.
Proof.
  move => P ext.
  elim: v;[> done|].
  move => e1 v' IH vfr.
  simpl.
  f_equal.
  - rewrite ext => //.
    move: vfr.
    simpl.
    by case /andP.
  - apply: IH.
    move: vfr; simpl; by case /andP.
Qed.

Lemma exp_var_map_map g fn (e : exp)
  : exp_var_map g (exp_var_map (fun n => var (fn n)) e) = exp_var_map (fun n => g (fn n)) e.
Proof using .
  elim: e => //.
  - simpl. intros.
    f_equal.
    rewrite map_comp.
    fold exp_var_map.
    elim: l H => //.
    simpl.
    move => h t vfr.
    inversion; subst.
    intros.
    f_equal => //.
    by apply: vfr.
  - simpl.
    move => pf e -> //.
Qed.

Lemma exp_var_map_ext f1 f2 (e : exp)
  : (forall n, f1 n = f2 n) -> exp_var_map f1 e = exp_var_map f2 e.
Proof.
  move => ext.
  elim: e; eauto.
  move => s l H.
  unfold exp_var_map.
  fold exp_var_map.
  f_equal.
  elim: l H => //.
  simpl.
  intros.
  inversion H0; subst.
  f_equal; auto.
  simpl.
  move => pf e -> //.
Qed.

Lemma exp_var_map_ext' f1 f2 (e : exp) m
  : ws_exp m e -> (forall n, n < m -> f1 n = f2 n) -> exp_var_map f1 e = exp_var_map f2 e.
Proof using .
  move => wse ext.
  elim: e wse ; eauto.
  move => n l H wsv.
  unfold exp_var_map.
  fold exp_var_map.
  f_equal.
  simpl in wsv.
  elim: l H wsv => //.
  simpl.
  intros.
  inversion H0; subst.
  move: wsv.
  case /andP.
  move /H3 ->.
  move /H.
  intros.
  f_equal.
  auto.
  
  simpl.
  intros; f_equal.
  apply: H; done.
Qed.

(*
Lemma shift1_decomp (e : exp) n : e^!(n.+1) = e^!n^!1.
Proof.
  elim: e n.
  - simpl; auto.
  - intros.
    unfold exp_shift.
    simpl.
    f_equal.
    rewrite -map_comp.
    eapply map_ext.
    intro e.
    simpl.
    rewrite exp_var_map_map.
    f_equal.
  - intros; simpl; f_equal; eauto.
Qed.
  
Theorem shift_preserves_ws (e : exp) (n m : nat)
  : ws_exp n e -> ws_exp (m + n) e^!m. 
Proof.
  elim: m e n.
  - intros; rewrite shiftz.
      by change (0 + n) with n.
  - intros.
    rewrite addSn.
    rewrite shift1_decomp.
    apply: shift1_preserves_ws.
    auto.
Qed.*)

(* TODO: needed?
Lemma lookup_in_shift_subst n' n m
  : n' < n -> var_lookup (shift_subst n m) n' = var (n' + m).
Proof.
  Print shift_subst.
  elim: n' n m.
  - case => //.
  - move => n IH.
    case => //.
    simpl.
    intros.
    change (n.+1 + m) with (n + m).+1.
    rewrite addnC.
    change (m + n).+1 with (m.+1 + n).
    rewrite addnC.
    eauto.
Qed. 

Theorem shift_subst_shift (e : exp) : forall n m, ws_exp n e ->  e [/shift_subst n m/] = e^!m.
Proof.
  elim: e.
  - unfold exp_shift.
    unfold exp_subst.
    unfold exp_var_map.
    intros; rewrite addnC;
    eapply lookup_in_shift_subst.
    auto.
  - intros.
    unfold exp_shift.
    unfold exp_subst.
    unfold exp_var_map.
    f_equal.
    pose H0' := H0.
    simpl in H0'.
    fold exp_var_map.
    apply: map_ext'.
    move => e ppf.
    apply: exp_var_map_ext'.
    exact ppf.
    move => n1 n1lt.
    rewrite addnC.
    eapply lookup_in_shift_subst.
    exact n1lt.
    done.
Qed.*)

(* TODO: is this true? if so, prove
Lemma id_subst {p} (e : exp p) : forall n m, e [/shift_subst n 0/] = e [/shift_subst m 0/].
*)

(*
Lemma extract_var_shift n : var n = (var 0)^!n.
Proof.
  elim: n; simpl; auto.
  intros.
  rewrite shift1_decomp.
  rewrite -H.
  auto.
Qed.
*)


(* TODO: is this needed? if so, prove
Lemma constr_shift_subst_comm e s n : e[/s/]%!n = e%!n[/s::%!n/].
Proof.
  elim: e s n.
  - elim ;intro_to subst; case => //.
  - intros; simpl;
      unfold exp_subst;
      unfold exp_var_map;
      fold exp_var_map;
      fold exp_subst.
    f_equal.
    fold exp_subst.
    elim: l H => //.
    simpl; intro_to and.
    case; intros.
    f_equal; eauto.
Qed.
*)

Fixpoint eq_lepf pf1 pf2 {struct pf1} : bool :=
  match pf1, pf2 with
  | lepf_by n1, lepf_by n2 => n1 == n2
  | lepf_subst pf1 pfs1, lepf_subst pf2 pfs2 =>
    (eq_lepf pf1 pf2) && (all2 eq_lepf pfs1 pfs2) 
  | lepf_refl, lepf_refl => true
  | lepf_trans pf11 pf12, lepf_trans pf21 pf22 =>
    (eq_lepf pf11 pf21) && (eq_lepf pf12 pf22)
  | lepf_conv pf11 pf12, lepf_conv pf21 pf22 =>
    (eq_lepf pf11 pf21) && (eq_lepf pf12 pf22)
  | _, _ => false
  end.

Ltac remember_and_case exp :=
  let H := fresh in
  let Heq := fresh in
  remember exp as H eqn:Heq; symmetry in Heq;
  case: H Heq.
  

Lemma eq_lepfP : forall pf1 pf2, reflect (pf1 = pf2) (eq_lepf pf1 pf2).
Proof.
  elim; intros until pf2; case: pf2; simpl.
  intros.
  all: try (intros; match goal with
             | |- context[reflect _ false] => constructor; easy
             | |- context[reflect _ true] => constructor; easy
             | |- context[?a == ?b] => remember_and_case (a== b); constructor
                    end).
  by move: H0 => /eqP ->.
  case.
  move /eqP.
  rewrite H0; done.
  give_up(*TODO: need improved IH*).
  intros; remember_and_case (eq_lepf l l1); simpl.
Admitted.


Definition lepf_eqMixin := Equality.Mixin eq_lepfP.

Canonical lepf_eqType := @Equality.Pack lepf lepf_eqMixin.
  
Fixpoint eq_exp e1 e2 {struct e1} : bool :=
  match e1, e2 with
  | var x, var y => x == y
  | con n1 l1, con n2 l2 =>
    (n1 == n2) && (all2 eq_exp l1 l2)
  | conv pf1 e1', conv pf2 e2' =>
    (pf1 == pf2) && (eq_exp e1' e2')
  | _,_ => false
  end.

(*
Lemma exp2_ind (P : exp -> exp -> Set)
  : (forall n m, P (var n) (var m)) ->
    (forall n c l, P (var n) (con c l)) ->
    (forall n c l, P (con c l) (var n)) ->
    (forall c1 c2, P (con c1 [::]) (con c2 [::])) ->
    (forall c1 c2 a l, P (con c1 [::]) (con c2 (a::l))) ->
    (forall c1 c2 a l, P (con c1 (a::l)) (con c2 [::])) ->
    (forall c1 c2 a1 a2 l1 l2,
        P a1 a2 ->
        P (con c1 l1) (con c2 l2) ->
        P (con c1 (a1::l1)) (con c2 (a2::l2))) ->
    forall e1 e2, P e1 e2.
Proof using .
  intro_to exp.
  elim.
  - intro_to exp; case; auto.
  - intro_to exp.
    case; auto.
    move => n0.
    elim: l X.
    + move => _; case; auto.
    + move => a l IH.
      simpl; case => pa fld.
      case; auto.
Qed.      *)

(*TODO: case neq does not use the right name*)
Tactic Notation "case_on_eqb" ident(a) ident(b) :=
  let neq := fresh "neq" in
  case neq: (a == b); constructor;
  [f_equal; apply /eqP
  | case => /eqP; rewrite neq].
  
(*
Lemma eq_exp_refl : forall e, eq_exp e e.
Proof.
  elim; simpl; auto.
  move => n.
  suff: n == n.
  move ->; simpl.
  elim; simpl; auto.
  intro_to and.
  case => eqaa fld.
  apply /andP.
  split; auto.
  elim: n; simpl; auto.
Qed.

Lemma all2_eq_exp_refl : forall l, all2 eq_exp l l.
  pose eqer := eq_exp_refl.
  elim; simpl; auto.
  intros; apply /andP; split; auto.
Qed.
*)
Lemma eq_expP : forall e1 e2, reflect (e1 = e2) (eq_exp e1 e2).
Proof.
(*  elim.
  - intro_to exp; case; simpl.
    + move => n0.
        by case_on_eqb n n0.
    + constructor; by case.
  - intro_to exp; case; simpl.
    + constructor; by case.
    + intros.
      case neq: (n == n0); simpl.
      * case alleq: (all2 eq_exp l l0).
        --constructor.
          f_equal.
            by apply /eqP; rewrite neq.
            elim: l X l0 alleq.
          ++ simpl; move => _; case; by auto.
          ++ simpl; move => a l IH.
             case => refla fld.
             case; try by auto.
             move => a0 l0.
             case /andP.
             move /refla => -> all2l.
             f_equal.
             eauto.
        -- constructor.
           case => _.
           elim: l X l0 alleq.
           ++ simpl; move => _; case; by auto.
          ++ simpl; move => a l IH.
             case => refla fld.
             case; try by auto.
             move => a0 l0.
             move /andP => oneof.
             case => aeq leq.
             apply oneof.
             split.
             rewrite aeq.
             apply: eq_exp_refl.
             rewrite leq.
             apply: all2_eq_exp_refl.
      * constructor.
        case; move /eqP; by rewrite neq.
Qed.*)
Admitted.

Definition exp_eqMixin := Equality.Mixin eq_expP.

Canonical proof_exp_eqType := @Equality.Pack exp exp_eqMixin.



Require Import String.
Section Printing.

  (* A lazily-written print nat fn *)
  Fixpoint printnat' fuel n : string :=
    match fuel with
    | 0 => "ERR"
    | fuel'.+1 =>
      match n with
      | 0 => "0"
      | 1 => "1"
      | 2 => "2"
      | 3 => "3"
      | 4 => "4"
      | 5 => "5"
      | 6 => "6"
      | 7 => "7"
      | 8 => "8"
      | 9 => "9"
      | _ => (printnat' fuel' (Nat.div n 10)) ++ (printnat' fuel' (Nat.modulo n 10))
      end
    end.

  Definition printnat x : string := printnat' (x.+1) x.

  Goal printnat 0 = "0"%string.
      by compute.
  Qed.
  
  Goal printnat 1 = "1"%string.
      by compute.
  Qed.
  
  Goal printnat 5 = "5"%string.
      by compute.
  Qed.
  
  Goal printnat 78 = "78"%string.
      by compute.
  Qed.
  
  Goal printnat 100 = "100"%string.
      by compute.
  Qed.
  
  Fixpoint print e : string :=
    match e with
    | var n => printnat n
    | con n s => "[" ++ printnat n ++ "|" ++ concat ";" (map print s) ++ "]"
    | conv pf e => "TODO: pfs; " ++ print e
    end.

  Goal print [1| (var 2); (var 2)] = "[1|2;2]"%string.
      by compute.
  Qed.

End Printing.

(* TODO: everything below
Lemma
  exp_subst_ind' (P : exp -> Prop) (Q : subst -> Prop)
  : (forall n,  P (var n)) ->
    (forall n s,  Q s -> P (con n s)) ->
    Q [::] ->
    (forall e s, P e -> Q s -> Q (e :: s)) ->
    forall e, P e.
Proof using .
  intros.
    elim: e; auto.
    move=> n.
    elim.
    auto.
    intros.
    simpl in H4.
    destruct H4.
    apply H0.
    apply H2; auto.
    clear H3.
    elim: l H5; auto.
    intros.
    destruct H5.
    apply H2; auto.
Qed.

Lemma
  exp_subst_ind (P : exp -> Prop) (Q : subst -> Prop)
  : (forall n,  P (var n)) ->
    (forall n s,  Q s -> P (con n s)) ->
    Q [::] ->
    (forall e s, P e -> Q s -> Q (e :: s)) ->
    (forall e, P e) /\ (forall s, Q s).
Proof using .
  intros.
  assert ( alleP : forall e, P e).
  apply (@exp_subst_ind' P Q); auto.
  split; auto.
  clear H0 H.
  suff: (forall e s, Q s -> Q (e :: s)).
  intro; elim; eauto.
  eauto.
Qed.

Lemma subst_cmp_size s1 s2 : size (subst_cmp s1 s2) = size s1.
Proof using .
  elim: s1; simpl; auto.
Qed.

Lemma exp_var_map_nth s' m s n
  : exp_var_map (var_lookup s') (nth (var m) s n)
    = nth (var_lookup s' m) (subst_cmp s s') n.
Proof using .
  elim: n s; intros until s; case: s => //=.
Qed.

Lemma var_lookup_cmp n s1 s2 : n < size s1 ->
                               var_lookup (subst_cmp s1 s2) n = exp_var_map (var_lookup s2) (var_lookup s1 n).
Proof using .
  unfold var_lookup at 1 3; unfold nth_level.
  rewrite !subst_cmp_size.
  move => nlt; pose p := nlt; move: p.
  case: (n < size s1) => //= _.
  rewrite exp_var_map_nth.
  move: nlt.
  rewrite -!(@subst_cmp_size s1 s2) => nlt.
  apply: set_nth_default.
  move: nlt.
  generalize (size (subst_cmp s1 s2)); case =>//.
  intros; rewrite subSS.
  apply: sub_ord_proof.
Qed.

Lemma subst_cmp_assoc'
  : (forall e s1 s2, ws_exp (size s1) e -> e[/subst_cmp s1 s2/] = e[/s1/][/s2/])
    /\ (forall s s1 s2, ws_subst (size s1) s -> subst_cmp (subst_cmp s s1) s2 = subst_cmp s (subst_cmp s1 s2)).
Proof using .
  apply exp_subst_ind; simpl; auto; intros.
  2: by rewrite !con_subst_cmp H.
  2: {
    move /andP in H1.
    destruct H1.
    rewrite H; auto.
    rewrite H0; auto.
  }
 intros.
 unfold exp_subst.
 simpl.
 by apply var_lookup_cmp.
Qed.

Lemma subst_cmp_assoc s s1 s2
  : List.fold_right (fun e : exp => andb (ws_exp (size s1) e)) true s ->
    subst_cmp (subst_cmp s s1) s2 = subst_cmp s (subst_cmp s1 s2).
Proof using .
    by eapply subst_cmp_assoc'.
Qed.

Lemma sep_subst_cmp e s1 s2 :  ws_exp (size s1) e -> e[/subst_cmp s1 s2/] = e[/s1/][/s2/].
Proof using .
    by eapply subst_cmp_assoc'.
Qed.

(*TODO: needed?
Fixpoint lift_subst sz n : subst :=
  match sz with
  | 0 => [::]
  | sz'.+1 => (var n)::(lift_subst sz' (n.+1))
  end.

Lemma lift_subst_lookup n n0 sz : n < sz -> var (n0 + n) = var_lookup (lift_subst sz n0) n.
Proof using .
elim: n sz n0.
    case; first easy; by simpl; intros; rewrite addn0.
    move => n IH.
    case; first easy.
    intros; simpl.
    rewrite -addSnnS.
    eauto.
Qed.

Lemma lift_is_subst sz e n : ws_exp sz e -> e^!n = e[/lift_subst sz n/].
Proof using .
  case: e; unfold exp_subst; unfold exp_shift; simpl; eauto using lift_subst_lookup.
  - intros.
    f_equal.
    apply: (map_ext' (P := ws_exp sz)); auto; intros.
    apply: (exp_var_map_ext' (m:=sz)); auto; intros.
    by apply: lift_subst_lookup.
Qed. 


Lemma subst_lift_is_subst sz s n : ws_subst sz s -> s^!!n = subst_cmp s (lift_subst sz n).
Proof using .
  elim: s n; simpl.
  - elim: sz; simpl; auto.
  - move => a l IH n /andP [wsa wsl].
    f_equal; eauto using lift_is_subst.
Qed.
*)

Fixpoint id_subst n : subst :=
  match n with
  | 0 => [::]
  | n'.+1 =>
    let s' := id_subst n' in
    (var (size s'))::s'
  end.

Lemma id_subst_size sz : size (id_subst sz) = sz.
Proof using .
  elim: sz => //=.
  intros; by f_equal.
Qed.

Lemma id_subst_lookup n sz : var_lookup (id_subst sz) n = var n.
Proof using .
  unfold var_lookup.
  unfold nth_level.
  rewrite id_subst_size.
  case nsz: (n < sz) => //.
  apply (level_ind (R:=fun m n => nth (var n) (id_subst sz) m = var n)); auto.
  intro m.
  elim: m n sz nsz; intros until sz; case: sz => //; simpl; intros.
  - f_equal.
    rewrite id_subst_size subn1.
    by rewrite <-pred_Sn.
  - rewrite !subSS.
    eauto.
Qed.    

Lemma id_subst_identity e sz : e[/id_subst sz/] = e.
Proof using .
  elim: e sz; intros; unfold exp_subst; simpl; first by apply id_subst_lookup.
  f_equal.
  elim: l H => //.
  simpl.
  intro_to and.
  case => [ aeq fld].
  f_equal; eauto.    
Qed.  
*)
