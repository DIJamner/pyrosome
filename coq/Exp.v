
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
Inductive exp (p : polynomial) : Type :=
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
  
Inductive ctx_var p : Type :=
| term_var : exp p -> ctx_var p
| sort_var : ctx_var p.

Arguments term_var {p} e.
Arguments sort_var {p}.

Definition ctx p := list (ctx_var p).

(* terms form a category over sorts w/ (empty or constant?) Γ *)
Inductive rule (p : polynomial) : Type :=
| sort :  ctx p -> exp p -> rule p
| term :  ctx p -> exp p -> exp p -> rule p
| sort_le : ctx p -> ctx p -> exp p -> exp p -> rule p
| term_le : ctx p -> ctx p -> exp p -> exp p -> exp p -> exp p -> rule p.

Bind Scope rule_scope with rule.
Delimit Scope rule_scope with rule.
Local Open Scope rule_scope.
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

Fixpoint exp_subst {p} (e : exp p) (s : subst p) : exp p :=
  match e with
  | var n => var_lookup s n
  | con n s' v => con n s' (Vector.map (fun e => exp_subst e s) v)
  end.

Notation "e [/ s /]" := (exp_subst e s) (at level 7, left associativity).

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
  | v :: c' => ws_ctx c' && ws_ctx_var (size c) v
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
  : forall {p} e (s : subst p) (c c' : ctx p),
    ws_exp (size c') e ->
    ws_subst (size c) s (size c') ->
    ws_exp (size c) (exp_subst e s).
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
