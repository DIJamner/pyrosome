Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Require Import String.
From Utils Require Import Utils.

Unset Elimination Schemes.
Inductive exp : Set :=
(* variable name *)
| var : string -> exp
(* Rule label, list of subterms*)
| con : string -> list exp -> exp.
Set Elimination Schemes.


(*Stronger induction principle w/ better subterm knowledge 
  TODO: not so necessary anymore I think? remove?
 *)
Fixpoint exp_ind
         (P : exp -> Prop)
         (IHV : forall n, P(var n))
         (IHC : forall n l,
             List.fold_right (fun t => and (P t)) True l ->
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
             List.fold_right (fun t => prod (P t)) unit l ->
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
       (forall n, P (var n)) ->
       (forall n l,
             List.fold_right (fun t => prod (P t)) unit l ->
             P (con n l))-> forall e : exp, P e.

Variant sort : Set := srt : string -> list exp -> sort.

Definition ctx : Set := named_list_set sort.

Definition subst : Set := named_list_set exp.

Definition subst_lookup (s : subst) (n : string) : exp :=
  named_list_lookup (var n) s n.

Arguments subst_lookup !s n/.

Definition ctx_lookup (c: ctx) (n : string) : sort :=
  named_list_lookup (srt "" [::]) c n.

Arguments ctx_lookup !c n/.


Fixpoint exp_var_map (f : string -> exp) (e : exp) : exp :=
  match e with
  | var n => f n
  | con n l => con n (map (exp_var_map f) l)
  end.

Arguments exp_var_map f !e /.

Definition exp_subst (s : subst) e : exp :=
  exp_var_map (subst_lookup s) e.

Arguments exp_subst s !e /.

Definition subst_cmp s1 s2 : subst := named_map (exp_subst s1) s2.
Arguments subst_cmp s1 s2 /.

(* Well-scoped languages
   Written as functions that decide the properties
   determines that variables (but not constructor symbols) are well-scoped
 *)
Fixpoint ws_exp (args : seq string) (e : exp) : bool :=
  match e with
  | var x => x \in args
  | con _ s => all (ws_exp args) s
  end.
Arguments ws_exp args !e/.

Definition ws_args args : list exp -> bool := all (ws_exp args).
Arguments ws_args args !s/.

Fixpoint ws_subst args (s : subst) : bool :=
  match s with
  | [::] => true
  | (n,e)::s' => fresh n s' && ws_exp args e && ws_subst args s'
  end.
Arguments ws_subst args !s/.

Definition ws_sort args (t : sort) : bool :=
  match t with srt _ s => ws_args args s end.
Arguments ws_sort args !t/.

Fixpoint ws_ctx (c : ctx) : bool :=
  match c with
  | [::] => true
  | (n,t) :: c' => fresh n c' && ws_sort (map fst c') t && ws_ctx c'
  end.
Arguments ws_ctx !c/.

Lemma ws_all_fresh_ctx c
  : ws_ctx c -> all_fresh c.
Proof using .
  elim: c; simpl; auto.
  case; intros; simpl in *.
  move: H0.
  move => /andP [] /andP [] fr wss wsc.
  apply /andP; split; auto.
Qed.

Class Substable (A : Set) : Set :=
  {
  apply_subst : subst -> A -> A;
  well_scoped : list string -> A -> bool;
  subst_assoc : forall s1 s2 a,
      well_scoped (map fst s2) a ->
      apply_subst s1 (apply_subst s2 a) = apply_subst (subst_cmp s1 s2) a
(* TODO: identity law*)
  }.

Arguments well_scoped {A}%type_scope {Substable} _%seq_scope !_.
Arguments apply_subst {A}%type_scope {Substable} _%seq_scope !_.

Notation "e [/ s /]" := (apply_subst s e) (at level 7, left associativity).

Lemma exp_subst_nil e : exp_subst [::] e = e.
Proof using .
  elim: e; simpl; auto.
  intro n.
  elim;simpl; auto.
  intros e s IH.
  case; intros eeq IHfold.
  move: (IH IHfold); case => ->.
  repeat f_equal; assumption.
Qed. 

Lemma named_map_subst_nil s : named_map (exp_subst [::]) s = s.
Proof using .
  elim s; simpl; auto.
  case; intros.
  simpl; f_equal.
  f_equal; rewrite exp_subst_nil; reflexivity.
  done.
Qed.

Lemma subst_lookup_map s1 s2 n
  : n \in (map fst s2) ->
          exp_subst s1 (subst_lookup s2 n) = subst_lookup (named_map (exp_subst s1) s2) n.
Proof using .
  elim: s2; intro_to is_true; simpl in *.
  { inversion. }
  {
    destruct a; simpl.
    rewrite in_cons.
    case neqs:(n==s); simpl.
    {
      move: neqs => /eqP => neq; subst.
      by rewrite !eqb_refl.
    }
    {
      move /H.
      cbn in neqs.
      by rewrite !neqs.
    }
  }
Qed.
  
Lemma exp_subst_assoc : forall s1 s2 a,
    ws_exp (map fst s2) a ->
    exp_subst s1 (exp_subst s2 a)
    = exp_subst (subst_cmp s1 s2) a.
Proof using .
  intros s1 s2 a.
  elim: a s1 s2; intros; simpl in *.
  { by apply subst_lookup_map. }
  {
    f_equal.
    elim: l H H0; intros; simpl in *; auto.
    move: H1 => /andP [] wse wsl.
    destruct H0.
    f_equal; eauto.
  }
Qed.  

Instance substable_exp : Substable exp :=
  {
  apply_subst := exp_subst;
  well_scoped := ws_exp;
  subst_assoc := exp_subst_assoc;
  }.
 
Lemma subst_subst_assoc : forall s1 s2 a,
    ws_subst (map fst s2) a ->
    subst_cmp s1 (subst_cmp s2 a)
    = subst_cmp (subst_cmp s1 s2) a.
Proof using .
  intros s1 s2 a.
  elim: a s1 s2; intros; simpl in *; auto.
  destruct a; simpl in *.
  move: H0 => /andP [] /andP []; intros.
  f_equal; eauto; f_equal; eauto using exp_subst_assoc.
Qed.

Instance substable_subst : Substable subst :=
  {
  apply_subst := subst_cmp;
  well_scoped := ws_subst;
  subst_assoc := subst_subst_assoc;
  }.

Definition args_subst s (a : list exp) := map (apply_subst s) a.
Arguments args_subst s !a/.

Lemma args_subst_assoc : forall s1 s2 a,
    ws_args (map fst s2) a ->
    args_subst s1 (args_subst s2 a)
    = args_subst (subst_cmp s1 s2) a.
Proof using .
  intros s1 s2 a.
  elim: a s1 s2; intros; simpl in *; auto.
  move: H0 => /andP []; intros.
  f_equal; eauto using exp_subst_assoc.
Qed.

Instance substable_args : Substable (list exp) :=
  {
  apply_subst := args_subst;
  well_scoped := ws_args;
  subst_assoc := args_subst_assoc;
  }.

Definition sort_subst (s : subst) (t : sort) : sort :=
  let (c, s') := t in srt c s'[/s/].
Arguments sort_subst s !t/.

Lemma sort_subst_assoc : forall s1 s2 a,
    ws_sort (map fst s2) a ->
    sort_subst s1 (sort_subst s2 a)
    = sort_subst (subst_cmp s1 s2) a.
Proof using .
  intros s1 s2; case; intros; simpl.
  f_equal; eauto using subst_assoc.
Qed.

Instance substable_sort : Substable sort :=
  { subst_assoc := sort_subst_assoc }.
    
(*

Lemma ws_lookup : forall d args (s : subst) n,
    ws_subst args s -> n \in map fst s -> ws_exp args (named_list_lookup d s n).
Proof.
  intros d args.
  elim; simpl; auto.
  case.
  intros n0 e0 s IH n.
  simpl ws_subst.


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
    case: IHB => IHB1 IHB2.
    apply /andP. split; [auto|].
    move: IHA -> => //=.
Qed.


Lemma shiftz (e : exp) : e^!0 = e.
Proof using .
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
Proof using .
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
*)

Definition eq_pr {A B} eq_a eq_b (p1 p2 : A*B) : bool :=
  let (a1,b1) := p1 in
  let (a2,b2) := p2 in
  (eq_a a1 a2) && (eq_b b1 b2).

Fixpoint eq_exp e1 e2 {struct e1} : bool :=
  match e1, e2 with
  | var x, var y => eqb x y
  | con n1 l1, con n2 l2 =>
    (eqb n1 n2) && (all2 eq_exp l1 l2)
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

*)

Lemma eq_expP : forall e1 e2, reflect (e1 = e2) (eq_exp e1 e2).
Admitted.
(*Proof.
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
Qed.*)        
                

Definition exp_eqMixin := Equality.Mixin eq_expP.

Canonical exp_eqType := @Equality.Pack exp exp_eqMixin.

Definition eq_sort (t1 t2 : sort) :=
  let (n1, s1) := t1 in
  let (n2, s2) := t2 in
  (n1 == n2) && (s1 == s2).

Lemma eq_sortP s1 s2 : reflect (s1 = s2) (eq_sort s1 s2).
Admitted.

Canonical sort_eqType := @Equality.Pack sort (Equality.Mixin eq_sortP).
(*

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

Definition exp_of_uint ui := var (Nat.of_uint ui).
Definition uint_of_exp e :=
  match e with
  | var n => Some (Nat.to_uint n)
  | _ => None
  end.

Declare Scope exp_scope.
Bind Scope exp_scope with exp.
Delimit Scope exp_scope with exp_scope.
Numeral Notation exp exp_of_uint uint_of_exp : exp_scope.

Arguments con n s%exp_scope.
*)

(* TODO: how many of these should be part of the substable class?*)
Lemma ws_exp_mono s (v : exp) n e : fresh n s -> well_scoped (map fst s) v -> v[/(n,e)::s/] = v[/s/].
Proof using .
  elim: v; intros; simpl in *.
  {
    suff: (n0 =? n = false)%string.
    { by move ->. }
    {
      apply /negP.
      apply /negP.
      eapply fresh_neq_in_fst; eauto.
    }
  }
  {
    f_equal.
    elim: l H H1; intros; simpl in *; auto.
    move: H2 => /andP []; intros.
    move: H1 => []; intros.
    f_equal; eauto.
  }
Qed.

Lemma ws_args_mono s (v : list exp) n e : fresh n s -> well_scoped (map fst s) v -> v[/(n,e)::s/] = v[/s/].
Proof using .
  elim: v; intros; simpl in *; auto.
  {
    move: H1 => /andP []; intros.
    f_equal; eauto using ws_exp_mono.
  }
Qed.

Lemma ws_sort_mono s (v : sort) n e : fresh n s -> well_scoped (map fst s) v -> v[/(n,e)::s/] = v[/s/].
Proof using .
  case: v; intros; simpl in *.
  f_equal; eauto using ws_args_mono.
Qed.

Lemma ws_subst_lookup args s n
  : well_scoped args s -> n \in map fst s -> well_scoped args (subst_lookup s n).
Proof using .
  elim: s; intros; simpl in *; break; auto.
  move: H1; rewrite in_cons; cbn.  
  case neq : (n=?s)%string; simpl; auto.
Qed.
  
Lemma ws_exp_subst args s (v : exp)
  : well_scoped args s -> well_scoped (map fst s) v -> well_scoped args v[/s/].
Proof using .
  elim: v; intros; simpl in *; auto using ws_subst_lookup.
  elim: l H H1; intros; simpl in *; break; auto.
  break_goal; auto.
Qed.  

Lemma ws_args_subst args s (v : list exp)
  : well_scoped args s -> well_scoped (map fst s) v -> well_scoped args v[/s/].
Proof using .
  elim: v; intros; simpl in *; auto; break.
  break_goal; auto using ws_exp_subst.
Qed.

Lemma ws_sort_subst args s (v : sort)
  : well_scoped args s -> well_scoped (map fst s) v -> well_scoped args v[/s/].
Proof using .
  case: v; intros; simpl in *; break; auto using ws_args_subst.
Qed.

Lemma ws_subst_subst args s (v : subst)
  : well_scoped args s -> well_scoped (map fst s) v -> well_scoped args v[/s/].
Proof using .
  elim: v; intros; break; simpl in *; break; auto.
  break_goal; auto using ws_exp_subst.
  erewrite fresh_iff_names_eq; eauto using named_map_fst_eq.
Qed.  

Ltac fold_Substable :=
  try change (named_map (exp_subst ?s') ?s) with s[/s'/];
  try change (exp_subst ?s ?e) with e[/s/];
  try change (sort_subst ?s ?e) with e[/s/];
  try change (subst_cmp ?s ?e) with e[/s/].


Lemma ws_subst_args args (s : subst)
  : well_scoped args s = (all_fresh s) && (well_scoped args (map snd s)).
Proof using .
  elim: s; simpl; auto.
  case; intros n0 e0 s IH; simpl.
  unfold well_scoped in IH; simpl in *.
  rewrite IH.
  ring.
Qed.
