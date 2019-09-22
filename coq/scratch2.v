
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
Inductive poly_fix (p : polynomial) : Type :=
  | var : nat -> poly_fix p
  | con : forall n, fst (nth zterm p n) ->
                     Vector.t (poly_fix p) (snd (nth zterm p n)) ->
                     poly_fix p.
Set Elimination Schemes.

Arguments var {p}.
Arguments con {p}.

(*Stronger induction principle w/ better subterm knowledge *)
Fixpoint poly_fix_ind {p}
         (P : poly_fix p -> Prop)
         (IHV : forall n, P(var n))
         (IHC : forall n s v,
             Vector.fold_right (fun t : poly_fix p => and (P t)) v True ->
             P (con n s v))
         (e : poly_fix p) { struct e} : P e :=
  match e with
  | var n => IHV n
  | con n s v =>
    let fix loop n v :=
        match v return Vector.fold_right (fun t => and (P t)) v True with
        | Vector.nil => I
        | Vector.cons e' n v' => conj (poly_fix_ind IHV IHC e') (loop n v')
        end in
    IHC n s v (loop _ v)
  end.

Notation "[*]" := (Vector.nil _).
Notation "[* x ]" := (Vector.cons _ _ x (Vector.nil _)).
Notation "[* x ; .. ; y ]" := (Vector.cons _ x _ .. (Vector.cons _ y _ (Vector.nil _)) ..).

Notation "[ n | s , v ]" := (con n s v).
Notation "[{ p } n | s , v ]" := (@con p n s v).


Definition test1 : polynomial := [:: (unit,1) ; (unit,2) ; (nat,0)].

Definition tvar (n : nat) : poly_fix test1 :=
  [{test1} 2 | n, [*]].

Definition prod_test : Vector.t nat 1 := [* 3].
Definition prod_test2 : Vector.t nat 3 := [* 3; 5; 4].

Definition tlam (e : poly_fix test1) : poly_fix test1 :=
  [{test1} 0 | tt , [* e]].

Definition tapp (e1 e2 : poly_fix test1) : poly_fix test1 :=
  [{test1} 1 | tt, [* e1; e2]].


Definition test1ex : poly_fix test1 := tlam (tlam (tapp (tvar 1) (tvar 0))).

Inductive ctxt_var p : Type :=
| term_var : poly_fix p -> ctxt_var p
| sort_var : ctxt_var p.

Definition ctxt p := list (ctxt_var p).
  
Definition sort_rule p : Type := ctxt p * poly_fix p.
  
Definition term_rule p : Type := ctxt p * poly_fix p * poly_fix p.

(* terms form a category over sorts w/ (empty or constant?) Γ *)
Definition sort_eq_rule p : Type := ctxt p * (poly_fix p * poly_fix p).

(* TODO: two sorts? *)
Definition term_eq_rule p : Type := ctxt p * (poly_fix p * poly_fix p) * poly_fix p.

(* TODO: inline all of these defs? probably not? *)
Inductive rule (p : polynomial) : Type :=
| sort : sort_rule p -> rule p
| term : term_rule p -> rule p
| sort_eq : sort_eq_rule p -> rule p
| term_eq : term_eq_rule p -> rule p.

Definition lang p := list (rule p).
  
(* syntax of single explicit substitutions *)
Definition subst_syn : polynomial :=
  [:: (nat, 0); (* var (deBruijn) *)
     (unit, 2) (*subst M[N/0] *)
  ].

Definition wf_sort_and_cong {p : polynomial} (wfs : sort_rule p) : lang p :=
  let (c, s) := wfs in
  [:: sort_eq (c, (s, s)); sort wfs].

Definition wf_term_and_cong {p : polynomial} (wft : term_rule p) : lang p :=
  let (ct, s) := wft in
  let (c, t) := ct in
  [:: term_eq (c, (t, t), s); term wft].



(*TODO: put notations in the right place*)

Notation "{s c |- s1 === s2 }" := (sort_eq (c, (s1, s2))) (at level 80).

Definition sub (m n : poly_fix subst_syn) : poly_fix subst_syn :=
  [{subst_syn} 1 | tt , [* m; n]].

Definition svar (n : nat) : poly_fix subst_syn :=
  [{subst_syn} 0 | n , [*]].

  (* equational theory of substitutions *)
Definition subst_lang : lang subst_syn :=
  [:: {s [:: sort_var _] |- sub (svar 0) (var 0) === var 0}]
    ++ (List.flat_map
     wf_sort_and_cong
     [:: ([:: sort_var _; sort_var _],
          [{subst_syn} 1 | tt, [* var 0; var 1]]);
        ([:: sort_var _; sort_var _; term_var (var 1)],
         [{subst_syn} 1 | tt , [* var 0; var 2]])])
    ++ (List.flat_map
          wf_term_and_cong
          [:: ([:: sort_var _; term_var (var 0); sort_var _],
               [{subst_syn} 1 | tt , [* var 1; var 2]],
              var 0)]).             
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

Definition psubst (p : polynomial) := seq (poly_fix p).

Fixpoint var_lookup {p} (c : psubst p) (n : nat) : poly_fix p :=
  match c , n with
  | [::], _ => var n (*keep the var if no substitution needed*)
  | e :: _, 0 => e (*use the element if one is found *)
  | _ :: c', n'.+1 => var_lookup c' n' (*otherwise decrease both and continue *)
  end.

Fixpoint exp_subst {p} (e : poly_fix p) (s : psubst p) : poly_fix p :=
  match e with
  | var n => var_lookup s n
  | con n s' v => con n s' (Vector.map (fun e => exp_subst e s) v)
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

Fixpoint ws_exp {p : polynomial} csz (e : poly_fix p) : bool :=
  match e with
  | var n => n < csz
  | con n s v => Vector.fold_right (fun e f => (ws_exp csz e) && f) v true
  end.

Definition ws_ctxt_var {p : polynomial} csz (v : ctxt_var p) : bool :=
  match v with
  | sort_var => true
  | term_var ty => ws_exp csz ty
  end.

Fixpoint ws_ctxt {p : polynomial} (c : ctxt p) : bool :=
  match c with
  | [::] => true
  | v :: c' => ws_ctxt c' && ws_ctxt_var (size c) v
  end.

Fixpoint ws_lang {p : polynomial} (l : lang p) : bool :=
  match l with
  |[::] => true
  | sort (c, s) :: l' => ws_lang l' && ws_ctxt c && ws_exp (size c) s
  | term (c, t, s) :: l' => ws_lang l' && ws_ctxt c && ws_exp (size c) t && ws_exp (size c) s
  | sort_eq (c, (s1,s2)) :: l' => ws_lang l' && ws_exp (size c) s1 && ws_exp (size c) s2
  | term_eq (c, (t1,t2), s) :: l' =>
    ws_lang l' && ws_exp (size c) t1 && ws_exp (size c) t2 && ws_exp (size c) s
  end.

(* replaces m variables with terms with n free vars*)
Definition ws_subst {p} n (s : psubst p) m : bool :=
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

Lemma ws_nth : forall p n (s : psubst p) m e n',
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

Lemma ws_lookup : forall p n (s : psubst p) (m n' : nat),
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
  : forall {p} e (s : psubst p) (c c' : ctxt p),
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

(* TODO: from here*)
Definition wf_ctxt {p : polynomial} (c : ctxt p) : Type := True.

Fixpoint wf_lang {p : polynomial} (l : lang p) : Prop :=
  match l with
  |[::] => True
  | sort (c, s) :: l' => wf_lang l' /\ wf_ctxt c /\ ws_exp c s
  | term _ :: l' => wf_lang l'
  | sort_eq _ :: l' => wf_lang l'
  | term_eq _ :: l' => wf_lang l'
  end.

(* This ought to have worked
Fixpoint ws_exp {p : polynomial} (c : ctxt p) (s : poly_ctx p) { struct s} : Prop :=
  match s with
  | Cvar n => n < length c
  | Ccon _ => True
  end
with ws_pf {p1 p2 : polynomial} (c : ctxt p1) (s : Ipoly_functor (poly_ctx p1) p2) { struct s} : Prop :=
       match s with
       | pffst _ _ _ _ s'  => ws_prd c s'
       | pfrst _ _ _ e' => ws_pf c e'
       end
with ws_prd {p : polynomial} {n : nat} (c : ctxt p) (s : Iprod_n (poly_ctx p) n) { struct s} : Prop :=
       match s with
       | prod0 => True
       | prodS _ t s' => ws_exp c t /\ ws_prd c s'
       end.
*)
