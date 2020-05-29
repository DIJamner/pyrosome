
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From excomp Require Import Utils.

Unset Elimination Schemes.
Inductive exp : Set :=
(* variable deBruijn index *)
| var : nat -> exp
(* Rule deBruijn level, list of subterms*)
| con : nat -> seq exp -> exp.
Set Elimination Schemes.


(*Stronger induction principle w/ better subterm knowledge 
  TODO: not so necessary anymore I think? remove?
*)
Fixpoint exp_ind
         (P : exp -> Prop)
         (IHV : forall n, P(var n))
         (IHC : forall n l,
             List.fold_right (fun t : exp => and (P t)) True l ->
             P (con n l))
         (e : exp) { struct e} : P e :=
  match e with
  | var n => IHV n
  | con n l =>
    let fix loop l :=
        match l return List.fold_right (fun t => and (P t)) True l with
        | [::] => I
        | e' :: l' => conj (exp_ind IHV IHC e') (loop l')
        end in
    IHC n l (loop l)
  end.

Fixpoint exp_rect
         (P : exp -> Type)
         (IHV : forall n, P(var n))
         (IHC : forall n l,
             List.fold_right (fun t : exp => prod (P t)) unit l ->
             P (con n l))
         (e : exp) { struct e} : P e :=
  match e with
  | var n => IHV n
  | con n l =>
    let fix loop l :=
        match l return List.fold_right (fun t => prod (P t)) unit l with
        | [::] => tt
        | e' :: l' => (exp_rect IHV IHC e', loop l')
        end in
    IHC n l (loop l)
  end.

Definition exp_rec := 
[eta exp_rect]
     : forall P : exp -> Set,
       (forall n : nat, P (var n)) ->
       (forall n l,
             List.fold_right (fun t : exp => prod (P t)) unit l ->
             P (con n l))-> forall e : exp, P e.

Notation "[ n | ]" := (con n [::]).
Notation "[ n | e ]" := (con n [:: e]).
Notation "[ n | e ; .. ; e' ]" := (con n (cons e .. (cons e' [::]) ..)).

Variant constr (T : Set) : Set :=
| ccon : nat -> seq T -> constr T.

Notation "[{ T } n | ]" := (ccon T n [::]).
Notation "[{ T } n | e ]" := (ccon T n [:: e]).
Notation "[{ T } n | e ; .. ; e' ]" := (ccon T n (cons e .. (cons e' [::]) ..)).

Definition Alg := constr exp -> exp.

Fixpoint alg_fn (a : Alg) (e : exp) : exp :=
  match e with
  | var n => var n
  | con n l => a (ccon n (map (alg_fn a) l))
  end.    

Definition id_alg : Alg := fun ce =>
  match ce with
  | ccon n l => con n l
  end.

(* TODO: uniform inheritance condition? this feels like it would be nice to have
Coercion id_alg : constr >-> exp. *)

Definition ctx := list exp.


Definition subst := seq exp.

Fixpoint var_lookup (c : subst) (n : nat) : exp :=
  match c , n with
  | [::], _ => var n (*keep the var if no substitution needed*)
  | e :: _, 0 => e (*use the element if one is found *)
  | _ :: c', n'.+1 => var_lookup c' n' (*otherwise decrease both and continue *)
  end.

Fixpoint exp_var_map (f : nat -> exp) (e : exp) : exp :=
  match e with
  | var n => f n
  | con n l => con n (map (exp_var_map f) l)
  end.

Definition exp_subst (s : subst) e : exp :=
  exp_var_map (var_lookup s) e.

Notation "e [/ s /]" := (exp_subst s e) (at level 7, left associativity).

Definition subst_cmp s1 s2 : subst := map (exp_subst s2) s1.


Lemma con_subst_cmp n s s0 : (con n s0)[/s/] = con n (subst_cmp s0 s).
Proof.
  unfold exp_subst.
  simpl.
  f_equal.
Qed.


Definition exp_shift (e : exp) (m : nat) : exp :=
  exp_var_map (fun n => var (m + n)) e.

Notation "e ^! n" := (exp_shift e n) (at level 7, left associativity).

Fixpoint shift_subst (sz start : nat) : subst :=
  match sz with
  | 0 => [::]
  | sz'.+1 => (var start)::(shift_subst sz' (start.+1))
  end.

(*TODO: this is in the library. Why can't I find it? *)
Lemma sub_0_r : forall n, n - 0 = n.
Proof.
  elim; done.
Qed.  

Lemma lookup_ge : forall c n, length c <= n -> var_lookup c n = var (n - size c).
Proof.
  elim.
  move => n _;
  rewrite sub_0_r //=.
  move => x l IH; elim.
  rewrite ltn0; done.
  move => n _.
  apply: IH.
Qed.

Lemma lookup_nth : forall c n, var_lookup c n = nth (var (n - size c)) c n.
Proof.
  elim.
  move => n;
  rewrite sub_0_r nth_nil //=.
  move => x l IH; elim;[done|].
  move => n _;
  apply: IH.
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
  | con n v => List.fold_right (fun e f => (ws_exp csz e) && f) true v
  end.

Fixpoint ws_ctx (c : ctx) : bool :=
  match c with
  | [::] => true
  | t :: c' => ws_ctx c' && ws_exp (size c') t
  end.


(* replaces m variables with terms with n free vars*)
Definition ws_subst n (s : subst) m : bool :=
  (List.fold_right (fun e b => ws_exp n e && b) true s) && (size s == m).


Lemma unandb : forall (a b : bool) (C : Prop), (a -> b -> C) <-> (a && b -> C).
Proof.
  move => a b C; split.
  - move => CF ab.
    apply andb_prop in ab.
    case: ab.
    done.
  - move => CF aa bb.
    apply CF.
    rewrite andb_true_intro //=.
Qed.

Lemma ws_nth : forall n (s : subst) m e n',
    ws_subst n s m -> ws_exp n e -> ws_exp n (nth e s n').
Proof.
  move => n ; elim.
  - move => m e; elim; [done|].
    move => n' IH //=.
  - move => x l IH m e.
    elim => [| n' _].
    + rewrite /ws_subst //=.
      repeat case /andb_prop.
      done.
    + rewrite /ws_subst //=.
      repeat case /andb_prop.
      move => _ lf wse.
      case: m wse => //= m.
      rewrite eqSS => wse.
      apply: IH.
      rewrite /ws_subst //=.
      apply andb_true_intro; split. 
      done.
      exact wse.
Qed.

Lemma ws_empty : forall n m, ws_subst n [::] m = (m == 0).
Proof.
  move => n m.
  rewrite /ws_subst //=.
Qed.

Lemma ws_lookup : forall n (s : subst) (m n' : nat),
    ws_subst n s m -> n' < m -> ws_exp n (var_lookup s n').
Proof.  
  move => n.
  elim.  
  - move => m;
    elim;
    move: ws_empty ->;
    [ move => /eqP -> //=
    | move => n' IH //= /eqP => -> //=].
  - move => e l IH m n'.
    rewrite /ws_subst => //=.
    (repeat case /andP) => wse sl sr.
    elim: n' => [ //= | n' _ n'lt].
    case: m sr n'lt => //= m.
    move: eqSS -> => n'lt ngm.
    apply: (IH m n') => //=.
    rewrite /ws_subst //=.
    move: n'lt ->.
    rewrite Bool.andb_true_r //=.
Qed.

Theorem subst_preserves_ws
  : forall e (s : subst) (csz csz' : nat),
    ws_exp csz' e ->
    ws_subst csz s csz' ->
    ws_exp csz (exp_subst s e).
Proof.
  move => e s c c' wse.
  move => wss.
  pose (wss' := wss).
  move: wss'.
  rewrite /ws_subst;
    case /andP.
  move => elem_ws size_eq.
  pose size_eq' := size_eq.
  move: size_eq' wse => /eqP <-.
  elim: e => //= => n.
  - apply: ws_lookup => //=;
    move: size_eq => /eqP -> //=.
  - elim => //= x l' IHA IHB.
    case /andP => xexp rexp.
    case: IHB => IHB1 IHB2.
    apply /andP. split; [auto|].
    move: IHA -> => //=.
Qed.


Lemma shiftz (e : exp) : e^!0 = e.
Proof.
  elim: e; simpl; auto.
  intros; simpl.
  unfold exp_shift.
  simpl.
  f_equal; auto.
  elim: l H.
  - by simpl; auto.
  - simpl.
    intros.
    f_equal.
    + destruct H0.
      rewrite  -{2}H0.
      by unfold exp_shift.
    + apply: H.
      destruct H0.
      done.
Qed.

Lemma shift1_preserves_ws (e : exp) (n : nat)
  : ws_exp n e -> ws_exp (n.+1) e^!1. 
Proof.
  elim: e n.
  - simpl; auto.      
  - simpl.
    intros until l.
    elim: l.
    + simpl; auto.
    + simpl.
      intros.
      case: H0 => H00 H01.
      move: H1; case /andP => wse H1.
      apply /andP.
      split; auto.
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
Proof.
  elim: e => //.
  - simpl. intros.
    f_equal.
    rewrite map_comp.
    elim: l H => //.
    simpl.
    move => h t vfr.
    case.
    intros.
    f_equal => //.
    by apply: vfr.
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
  case: H0 => -> IH.
  f_equal.
  auto.
Qed.

Lemma exp_var_map_ext' f1 f2 (e : exp) m
  : ws_exp m e -> (forall n, n < m -> f1 n = f2 n) -> exp_var_map f1 e = exp_var_map f2 e.
Proof.
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
  case: H0 => IH1 IH.
  move: wsv.
  case /andP.
  move /IH1 ->.
  move /H.
  intros.
  f_equal.
  auto.
Qed.
  
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
Qed.

Lemma lookup_in_shift_subst n' n m
  : n' < n -> var_lookup (shift_subst n m) n' = var (n' + m).
Proof.
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
Qed.

(* TODO: is this true? if so, prove
Lemma id_subst {p} (e : exp p) : forall n m, e [/shift_subst n 0/] = e [/shift_subst m 0/].
*)

Lemma extract_var_shift n : var n = (var 0)^!n.
Proof.
  elim: n; simpl; auto.
  intros.
  rewrite shift1_decomp.
  rewrite -H.
  auto.
Qed.


(*TODO: how to do with levels?*)
Fixpoint constr_shift n e :=
  match e with
  | var x => var x
  | con m l => con (n + m) (map (constr_shift n) l)
  end.


Notation "e %! n" := (constr_shift n e) (at level 7).

Notation "e ::%! n" := (map (constr_shift n) e) (at level 7).

Lemma constr_shift0 e : e%!0 = e.
Proof.
  elim: e => //.
  intros; simpl.
  f_equal.
  elim: l H => //.
  simpl; intros.
  case: H0 => H01 H02; f_equal; auto.
Qed.

Lemma map_constr_shift0 s : s::%!0 = s.
  elim: s => //.
  intros; simpl; f_equal; move: constr_shift0; auto.
Qed.
  
Lemma constr_shift_shift e n m : e%!n %!m = e%!(n + m).
Proof.
  elim: e => //.
  intros;
    simpl;
    f_equal.
  - ring.
  - elim: l H => //; simpl; intros.
    rewrite -> H;
      case: H0; intros.
    f_equal; auto.
    auto.
Qed.

Lemma map_constr_shift_shift l n m
  : l ::%! n ::%! m = l::%!(n+m).
Proof.
  elim: l => //.
  simpl.
  move => a l ->.
  f_equal; move: constr_shift_shift; auto.
Qed.
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

Fixpoint eq_exp e1 e2 {struct e1} : bool :=
  match e1, e2 with
  | var x, var y => x == y
  | con n1 l1, con n2 l2 =>
    (n1 == n2) && (all2 eq_exp l1 l2)
  | _,_ => false
  end.

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
Proof.
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
Qed.      

(*TODO: case neq does not use the right name*)
Tactic Notation "case_on_eqb" ident(a) ident(b) :=
  let neq := fresh "neq" in
  case neq: (a == b); constructor;
  [f_equal; apply /eqP
  | case => /eqP; rewrite neq].
  

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

Lemma eq_expP : forall e1 e2, reflect (e1 = e2) (eq_exp e1 e2).
Proof.
  elim.
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
Qed.

Definition exp_eqMixin := Equality.Mixin eq_expP.

Canonical exp_eqType := @Equality.Pack exp exp_eqMixin.

(* TODO: how to do for levels? any different?*)
(* TODO: write a predlike version?/nonoption?*)
Fixpoint constr_downshift n e : option exp :=
  match e with
  | var x => Some (var x)
  | con m l =>
    if n <= m
    then Option.map (con (m - n)) (try_map (constr_downshift n) l)
    else None
  end.

Lemma add_sub n n0 : n0 + n - n0 = n.
Proof.
  elim: n0 => //=.
  rewrite sub_0_r.
  by compute.
Qed.
  
Lemma downshift_left_inverse e n : constr_downshift n e%!n = Some e.
Proof.
  elim: e n; [by simpl|].
  intros; simpl.
  rewrite leq_addr.
  rewrite try_map_map_distribute.
  change (Some (con n l)) with (omap (con n) (Some l)).
  f_equal.
  f_equal; by apply add_sub.
  elim: l H => //=.
  intros.
  case: H0 => shifta shiftl.
  rewrite shifta.
  specialize (H shiftl).
  rewrite H.
  by compute.
Qed.

Lemma try_map_downshift_left_inverse l n : try_map (constr_downshift n) l::%!n = Some l.
Proof.
  elim: l => //=; intros.
  rewrite downshift_left_inverse H.
  by compute.
Qed.

Lemma add_inj_r n m1 m2 : n + m1 = n + m2 -> m1 = m2.
Proof.
  elim: n => //=.
  eauto.
Qed.
  
Lemma constr_shift_inj e1 e2 n : e1 %!n = e2 %!n -> e1 = e2.
Proof.
  elim: e1 e2; intro_to exp; case => //=.
  move => n1 l0.
  case.
  move /add_inj_r -> => shift_eq.
  f_equal.
  move: shift_eq.
  elim: l l0 H; intros until l0; case: l0 => //=.
  intro_to and.
  case => IH_a0 IHl.
  case.
  move /IH_a0 -> => shifteq.
  f_equal.
  eauto.
Qed.

Lemma seq_constr_shift_inj l1 l2 n : l1 ::%!n = l2 ::%!n -> l1 = l2.
Proof.
  elim: l1 l2; intros until l2; case: l2 => //=.
  move => a0 l0.
  case.
  by move /constr_shift_inj -> => /H ->.
Qed.


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
    end.

  Goal print [1| (var 2); (var 2)] = "[1|2;2]"%string.
      by compute.
  Qed.

End Printing.
