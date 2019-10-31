
Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Require Vector.

Definition polynomial := seq (Set * nat).
Print nth.

Definition zterm : Set * nat := (Empty_set , 0).


Unset Elimination Schemes.
Inductive exp (p : polynomial) : Set :=
  | var : nat -> exp p
  | con : forall n, fst (nth zterm p n) ->
                     Vector.t (exp p) (snd (nth zterm p n)) ->
                     exp p.
Set Elimination Schemes.

Arguments var {p}.
Arguments con {p}.

(*Stronger induction principle w/ better subterm knowledge *)
Fixpoint exp_ind {p}
         (P : exp p -> Prop)
         (IHV : forall n, P(var n))
         (IHC : forall n s v,
             Vector.fold_right (fun t : exp p => and (P t)) v True ->
             P (con n s v))
         (e : exp p) { struct e} : P e :=
  match e with
  | var n => IHV n
  | con n s v =>
    let fix loop n v :=
        match v return Vector.fold_right (fun t => and (P t)) v True with
        | Vector.nil => I
        | Vector.cons e' n v' => conj (exp_ind IHV IHC e') (loop n v')
        end in
    IHC n s v (loop _ v)
  end.

Notation "[*]" := (Vector.nil _).
Notation "[* x ]" := (Vector.cons _ _ x (Vector.nil _)).
Notation "[* x ; .. ; y ]" := (Vector.cons _ x _ .. (Vector.cons _ y _ (Vector.nil _)) ..).

Notation "[ n | s , v ]" := (con n s v).
Notation "[{ p } n | s , v ]" := (@con p n s v).

Variant constr p (T : Set) :=
| ccon : forall n, fst (nth zterm p n) ->
                   Vector.t T (snd (nth zterm p n)) -> constr p T.

Notation "[{ p , T }> n | s , v ]" := (@ccon p T n s v).

Definition Alg p1 p2 := constr p1 (exp p2) -> exp p2.

Fixpoint alg_fn {p1 p2} (a : Alg p1 p2) (e : exp p1) : exp p2 :=
  match e with
  | var n => var n
  | con n s v => a (ccon s (Vector.map (alg_fn a) v))
  end.
    

Definition id_alg {p} : Alg p p := fun ce =>
  match ce with
  | ccon n s v => con n s v
  end.

(* TODO: uniform inheritance condition? this feels like it would be nice to have
Coercion id_alg : constr >-> exp. *)

Section ExpTest.
  Definition test1 : polynomial := [:: (unit,1) ; (unit,2) ; (nat,0)].
  
  Definition tvar (n : nat) : exp test1 :=
    [{test1} 2 | n, [*]].
  
  Definition prod_test : Vector.t nat 1 := [* 3].
  Definition prod_test2 : Vector.t nat 3 := [* 3; 5; 4].
  
  Definition tlam (e : exp test1) : exp test1 :=
    [{test1} 0 | tt , [* e]].
  
  Definition tapp (e1 e2 : exp test1) : exp test1 :=
    [{test1} 1 | tt, [* e1; e2]].
  
  Definition test1ex : exp test1 := tlam (tlam (tapp (tvar 1) (tvar 0))).
End ExpTest.
  
Inductive ctx_var p : Set :=
| term_var : exp p -> ctx_var p
| sort_var : ctx_var p.

Arguments term_var {p} e.
Arguments sort_var {p}.

Definition ctx_var_map {p1 p2} (f : exp p1 -> exp p2) (v : ctx_var p1) : ctx_var p2 :=
  match v with
  | sort_var => sort_var
  | term_var t => term_var (f t)
  end.

Definition ctx p := list (ctx_var p).

(* terms form a category over sorts w/ (empty or constant?) Γ *)
Inductive rule (p : polynomial) : Type :=
| sort :  ctx p -> exp p -> rule p
| term :  ctx p -> exp p -> exp p -> rule p
| sort_le : ctx p -> ctx p -> exp p -> exp p -> rule p
| term_le : ctx p -> ctx p -> exp p -> exp p -> exp p -> exp p -> rule p.

Definition rule_map {p1 p2} (f : exp p1 -> exp p2) r : rule p2 :=
  match r with
| sort c t => sort (List.map (ctx_var_map f) c) (f t)
| term c e t => term (List.map (ctx_var_map f) c) (f e) (f t)
| sort_le c1 c2 t1 t2 =>
  sort_le (List.map (ctx_var_map f) c1) (List.map (ctx_var_map f) c2) (f t1) (f t2)
| term_le  c1 c2 e1 e2 t1 t2 =>
  term_le (List.map (ctx_var_map f) c1) (List.map (ctx_var_map f) c2)
          (f e1) (f e2)
          (f t1) (f t2)
  end.

Bind Scope rule_scope with rule.
Delimit Scope rule_scope with rule.
Open Scope rule_scope.
Notation "{< c1 <# c2 |- s1 <# s2 }" := (sort_le c1 c2 s1 s2) (at level 80) : rule_scope.
Notation "{< c |- s1 <# s2 }" := (sort_le c c s1 s2) (at level 80):rule_scope.
Notation "{< c |- s }" := (sort_le c c s s) (at level 80):rule_scope.
Notation "{< c1 <# c2 |- e1 <# e2 .: s1 <# s2 }" :=
  (term_le c1 c2 e1 e2 s1 s2) (at level 80) : rule_scope.
Notation "{< c |- e1 <# e2 .: s1 <# s2 }" :=
  (term_le c c e1 e2 s1 s2) (at level 80) : rule_scope.
Notation "{< c |- e1 <# e2 .: s }" :=
  ({< c |- e1 <# e2 .: s <# s}) (at level 80) : rule_scope.
Notation "{< c |- e .: s }" := 
  ({< c |- e <# e.: s}) (at level 80) : rule_scope.
Notation "{| c |- s }" := 
  (sort c s) (at level 80) : rule_scope.
Notation "{| c |- e .: s }" := 
  (term c e s) (at level 80) : rule_scope.

Definition lang p := list (rule p).

Section SynExample.
  (*EXAMPLE*)
  (* syntax of single explicit substitutions *)
  Definition subst_syn : polynomial :=
    [:: (nat, 0); (* var (deBruijn) *)
       (unit, 2) (*subst M[N/0] *)
    ].
  
  Definition sub (m n : exp subst_syn) : exp subst_syn :=
    [{subst_syn} 1 | tt , [* m; n]].
  
  Definition svar (n : nat) : exp subst_syn :=
    [{subst_syn} 0 | n , [*]].
  
  (* equational theory of substitutions *)
  Definition subst_lang : lang subst_syn :=
    [:: {< [:: sort_var] |- sub (svar 0) (var 0) <# var 0};
       {<[:: sort_var; sort_var] |- [{subst_syn} 1 | tt, [* var 0; var 1]]};
       {<[:: sort_var; sort_var; term_var (var 1)] |- [{subst_syn} 1 | tt, [* var 0; var 2]]};
       {<[:: sort_var; term_var (var 0); sort_var] |-
        [{subst_syn} 1 | tt, [* var 1; var 2]] .: var 0};
       {<[:: sort_var; term_var (var 0); sort_var; term_var (var 2)] |-
        [{subst_syn} 1 | tt, [* var 1; var 3]] .: var 0}
    ].

  (*TODO: finish axioms
    (wf_sort_and_cong ([:: sort_var _; sort_var _],
    Ccon [++ tt | [* Cvar _ 0; Cvar _ 1]]))
    ++ (wf_sort_and_cong ([:: sort_var _; sort_var _; term_var (Cvar _ 1)],
    Ccon [++ tt | [* Cvar _ 0; Cvar _ 2]]))
    ++ (wf_sort_and_cong ([:: sort_var _; term_var (Cvar _ 0); sort_var _],
    Ccon [++ tt | [* Cvar _ 1; Cvar _ 2]]))
      ++ (wf_sort_and_cong ([:: sort_var _; term_var (Cvar _ 0); sort_var _; term_var (Cvar _ 2)],
      Ccon [++ tt | [* Cvar _ 1; Cvar _ 3]])).
   *)
End SynExample.
  
Definition subst (p : polynomial) := seq (exp p).

Fixpoint var_lookup {p} (c : subst p) (n : nat) : exp p :=
  match c , n with
  | [::], _ => var n (*keep the var if no substitution needed*)
  | e :: _, 0 => e (*use the element if one is found *)
  | _ :: c', n'.+1 => var_lookup c' n' (*otherwise decrease both and continue *)
  end.

Fixpoint exp_var_map {p} (f : nat -> exp p) (e : exp p) : exp p :=
  match e with
  | var n => f n
  | con n s v => con n s (Vector.map (exp_var_map f) v)
  end.

Definition exp_subst {p} (e : exp p) (s : subst p) : exp p :=
  exp_var_map (var_lookup s) e.

Notation "e [/ s /]" := (exp_subst e s) (at level 7, left associativity).

Definition exp_shift {p} (e : exp p) (m : nat) : exp p :=
  exp_var_map (fun n => var (m + n)) e.

Notation "e ^! n" := (exp_shift e n) (at level 7, left associativity).

Fixpoint shift_subst (sz start : nat) : forall {p}, subst p :=
  match sz with
  | 0 => fun p => [::]
  | sz'.+1 => fun p => (var start)::(shift_subst sz' (start.+1))
  end.

(*TODO: this is in the library. Why can't I find it? *)
Lemma sub_0_r : forall n, n - 0 = n.
Proof.
  elim; done.
Qed.  

Lemma lookup_ge : forall p c n, length c <= n -> @var_lookup p c n = var (n - size c).
Proof.
  move => p; elim.
  move => n _;
  rewrite sub_0_r //=.
  move => x l IH; elim.
  rewrite ltn0; done.
  move => n _.
  apply: IH.
Qed.

Lemma lookup_nth : forall p c n, @var_lookup p c n = nth (var (n - size c)) c n.
Proof.
  move => p; elim.
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
 *)

Fixpoint ws_exp {p : polynomial} csz (e : exp p) : bool :=
  match e with
  | var n => n < csz
  | con n s v => Vector.fold_right (fun e f => (ws_exp csz e) && f) v true
  end.

Definition ws_ctx_var {p : polynomial} csz (v : ctx_var p) : bool :=
  match v with
  | sort_var => true
  | term_var ty => ws_exp csz ty
  end.

Fixpoint ws_ctx {p : polynomial} (c : ctx p) : bool :=
  match c with
  | [::] => true
  | v :: c' => ws_ctx c' && ws_ctx_var (size c') v
  end.

Fixpoint ws_lang {p : polynomial} (l : lang p) : bool :=
  match l with
  |[::] => true
  | {| c |- s} :: l' => ws_lang l' && ws_exp (size c) s
  | {| c |- s .: t} :: l' => ws_lang l' && ws_exp (size c) s && ws_exp (size c) t
  | {< c1 <# c2 |- s1 <# s2} :: l' => ws_lang l' && ws_exp (size c1) s1 && ws_exp (size c2) s2
  | {< c1 <# c2 |- e1 <# e2 .: s1 <# s2} :: l' =>
    ws_lang l' && ws_exp (size c1) e1 && ws_exp (size c2) e2
            && ws_exp (size c1) s1 && ws_exp (size c2) s2
  end%rule.

(* replaces m variables with terms with n free vars*)
Definition ws_subst {p} n (s : subst p) m : bool :=
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

Lemma ws_nth : forall p n (s : subst p) m e n',
    ws_subst n s m -> ws_exp n e -> ws_exp n (nth e s n').
Proof.
  move => p n ; elim.
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

Lemma ws_empty : forall p n m, @ws_subst p n [::] m = (m == 0).
Proof.
  move => p n m.
  rewrite /ws_subst //=.
Qed.

Lemma ws_lookup : forall p n (s : subst p) (m n' : nat),
    ws_subst n s m -> n' < m -> ws_exp n (var_lookup s n').
Proof.  
  move => p n.
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

Ltac ws_simpl :=
  match goal with
    (* break up ws_subst *)
    [ |- is_true (ws_subst _ _ _) -> _] =>
    rewrite /ws_subst;
    case /andP
  end.


Theorem subst_preserves_ws
  : forall {p} e (s : subst p) (csz csz' : nat),
    ws_exp csz' e ->
    ws_subst csz s csz' ->
    ws_exp csz (exp_subst e s).
Proof.
  move => p e s c c' wse.
  move => wss.
  pose (wss' := wss).
  move: wss'.
  ws_simpl.
  move => elem_ws size_eq.
  pose size_eq' := size_eq.
  move: size_eq' wse => /eqP <-.
  elim: e => //= => n.
  - apply: ws_lookup => //=;
    move: size_eq => /eqP -> //=.
  - move => _.
    elim => //= x n' v IHA IHB.
    case /andP => xexp rexp.
    case: IHB => IHB1 IHB2.
    apply /andP. split; [auto|].
    move: IHA -> => //=.
Qed.


Lemma shiftz {p} (e : exp p) : e^!0 = e.
Proof.
  elim: e; simpl; auto.
  intros; simpl.
  unfold exp_shift.
  simpl.
  f_equal; auto.
  elim: v H.
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

Lemma shift1_preserves_ws {p} (e : exp p) (n : nat)
  : ws_exp n e -> ws_exp (n.+1) e^!1. 
Proof.
  elim: e n.
  - simpl; auto.      
  - simpl.
    intros until v.
    elim: v.
    + simpl; auto.
    + simpl.
      intros.
      case: H0 => H00 H01.
      move: H1; case /andP => wse H1.
      apply /andP.
      split; auto.
Qed.


Lemma vec_map_map {T1 T2 T3} (g : T2 -> T3) (f : T1 -> T2) {n} (v : Vector.t T1 n)
  : Vector.map g (Vector.map f v) = Vector.map (fun x => g (f x)) v.
Proof.
  elim: v => //.
  intros.
  simpl.
    by rewrite H.
Qed.

Lemma vec_map_ext {B C : Type} (f g : B -> C) n (v : Vector.t B n)
  : (forall e, f e = g e) -> Vector.map f v = Vector.map g v.
Proof.
  move => ext.
  elim: v; first done.
  move => e1 n' v' IH.
  simpl.
    by rewrite ext IH.
Qed.

Lemma vec_map_ext' {B C : Type} (f g : B -> C) n (v : Vector.t B n)
  : forall (P : B -> bool),
    (forall e, P e -> f e = g e) ->
    Vector.fold_right (fun e => [eta andb (P e)]) v true ->
    Vector.map f v = Vector.map g v.
Proof.
  move => P ext.
  elim: v;[> done|].
  move => e1 n' v' IH vfr.
  simpl.
  f_equal.
  - rewrite ext => //.
    move: vfr.
    simpl.
    by case /andP.
  - apply: IH.
    move: vfr; simpl; by case /andP.
Qed.

Lemma exp_var_map_map {p} g fn (e : exp p)
  : exp_var_map g (exp_var_map (fun n => var (fn n)) e) = exp_var_map (fun n => g (fn n)) e.
Proof.
  elim: e => //.
  - simpl. intros.
    f_equal.
    rewrite vec_map_map.
    elim: v H => //.
    simpl.
    move => h n' t vfr.
    case.
    intros.
    f_equal => //.
    by apply: vfr.
Qed.    

Lemma exp_var_map_ext {p} f1 f2 (e : exp p)
  : (forall n, f1 n = f2 n) -> exp_var_map f1 e = exp_var_map f2 e.
Proof.
  move => ext.
  elim: e; eauto.
  move => n s v H.
  unfold exp_var_map.
  fold (@exp_var_map p).
  f_equal.
  elim: v H => //.
  simpl.
  intros.
  case: H0 => -> IH.
  f_equal.
  auto.
Qed.

Lemma exp_var_map_ext' {p} f1 f2 (e : exp p) m
  : ws_exp m e -> (forall n, n < m -> f1 n = f2 n) -> exp_var_map f1 e = exp_var_map f2 e.
Proof.
  move => wse ext.
  elim: e wse ; eauto.
  move => n s v H wsv.
  unfold exp_var_map.
  fold (@exp_var_map p).
  f_equal.
  simpl in wsv.
  elim: v H wsv => //.
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
  
Lemma shift1_decomp {p} (e : exp p) n : e^!(n.+1) = e^!n^!1.
Proof.
  elim: e n.
  - simpl; auto.
  - intros.
    unfold exp_shift.
    simpl.
    f_equal.
    rewrite vec_map_map.
    apply: vec_map_ext.
    intro e.
    rewrite exp_var_map_map.
    f_equal.
Qed.
  
Theorem shift_preserves_ws {p} (e : exp p) (n m : nat)
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
  : n' < n -> forall p, @var_lookup p (shift_subst n m) n' = var (n' + m).
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

Theorem shift_subst_shift {p} (e : exp p) : forall n m, ws_exp n e ->  e [/shift_subst n m/] = e^!m.
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
    fold (@exp_var_map p).
    apply: vec_map_ext'.
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
