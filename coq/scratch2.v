
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

Arguments term_var {p} e.
Arguments sort_var {p}.

Definition ctxt p := list (ctxt_var p).

(* terms form a category over sorts w/ (empty or constant?) Γ *)
(* Well-typed sorts are those which are related to themselves by the sort rules of a language*)
Definition sort_rule p : Type := (ctxt p * ctxt p) * (poly_fix p * poly_fix p).

(* Well-typed terms are those which are related to themselves by the sort rules of a language*)
Definition term_rule p : Type :=
  (ctxt p * ctxt p) * (poly_fix p * poly_fix p) * (poly_fix p * poly_fix p).

(* TODO: inline these or no? *)
Inductive rule (p : polynomial) : Type :=
| sort : ctxt p -> ctxt p -> poly_fix p -> poly_fix p -> rule p
| term : ctxt p -> ctxt p -> poly_fix p -> poly_fix p -> poly_fix p -> poly_fix p ->  rule p.

Bind Scope rule_scope with rule.
Delimit Scope rule_scope with rule.
Local Open Scope rule_scope.
Notation "{r c1 <# c2 |- s1 <# s2 }" := (sort c1 c2 s1 s2) (at level 80) : rule_scope.
Notation "{r c |- s1 <# s2 }" := (sort c c s1 s2) (at level 80):rule_scope.
Notation "{r c |- s }" := (sort c c s s) (at level 80):rule_scope.
Notation "{r c1 <# c2 |- e1 <# e2 .: s1 <# s2 }" :=
  (term c1 c2 e1 e2 s1 s2) (at level 80) : rule_scope.
Notation "{r c |- e1 <# e2 .: s1 <# s2 }" :=
  (term c c e1 e2 s1 s2) (at level 80) : rule_scope.
Notation "{r c |- e1 <# e2 .: s }" :=
  ({r c |- e1 <# e2 .: s <# s}) (at level 80) : rule_scope.
Notation "{r c |- e .: s }" := 
  ({r c |- e <# e.: s}) (at level 80) : rule_scope.

Definition lang p := list (rule p).

(*EXAMPLE*)
(* syntax of single explicit substitutions *)
Definition subst_syn : polynomial :=
  [:: (nat, 0); (* var (deBruijn) *)
     (unit, 2) (*subst M[N/0] *)
  ].

Definition sub (m n : poly_fix subst_syn) : poly_fix subst_syn :=
  [{subst_syn} 1 | tt , [* m; n]].

Definition svar (n : nat) : poly_fix subst_syn :=
  [{subst_syn} 0 | n , [*]].

  (* equational theory of substitutions *)
Definition subst_lang : lang subst_syn :=
  [:: {r [:: sort_var] |- sub (svar 0) (var 0) <# var 0};
     {r[:: sort_var; sort_var] |- [{subst_syn} 1 | tt, [* var 0; var 1]]};
     {r[:: sort_var; sort_var; term_var (var 1)] |- [{subst_syn} 1 | tt, [* var 0; var 2]]};
     {r[:: sort_var; term_var (var 0); sort_var] |-
      [{subst_syn} 1 | tt, [* var 1; var 2]] .: var 0};
     {r[:: sort_var; term_var (var 0); sort_var; term_var (var 2)] |-
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
  | {r c1 <# c2 |- s1 <# s2} :: l' => ws_lang l' && ws_exp (size c1) s1 && ws_exp (size c2) s2
  | {r c1 <# c2 |- e1 <# e2 .: s1 <# s2} :: l' =>
    ws_lang l' && ws_exp (size c1) e1 && ws_exp (size c2) e2
            && ws_exp (size c1) s1 && ws_exp (size c2) s2
  end%rule.

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
(* We could embed well-scopedness in bool, but well-typedness can be undecideable,
   so we leave it in Prop.
   Some constructors take in more presuppositions than strictly necessary
   (i.e. they can be derived from other arguments). This is a conscious design choice.
   It is easier to devise secondary "constructor" functions that perform these
   derivations than to do the mutually inductive proof that such derivations exist.
 *)
(* TODO: build in transitivity? *)
Inductive wf_sort {p} : lang p -> ctxt p -> ctxt p -> poly_fix p -> poly_fix p -> Prop :=
| wf_sort_by : forall l c1 c2 t1 t2 s1 s2 c1' c2',
    (* presuppositions *)
    wf_lang l ->
    wf_ctxt l c1 c2 ->
    (* well-formed input *)
    wf_sort l c1 c2 t1 t2 ->
    wf_subst l c1 c2 s1 s2 c1' c2' ->
    List.In ({r c1' <# c2'|- t1 <# t2}%rule) l ->
    wf_sort l c1 c2 (exp_subst t1 s1) (exp_subst t2 s2)
| wf_sort_trans : forall l c1 c2 c3 t1 t2 t3,
    (* presuppositions *)
    wf_lang l ->
    wf_ctxt l c1 c3 ->
    (* well-formed input *)
    wf_sort l c1 c2 t1 t2 ->
    wf_sort l c2 c3 t2 t3 ->
    wf_sort l c1 c3 t1 t3
with wf_term {p} : lang p ->
                   ctxt p -> ctxt p ->
                   poly_fix p -> poly_fix p ->
                   poly_fix p -> poly_fix p -> Prop :=
| wf_term_by : forall l c1 c2 e1 e2 t1 t2 s1 s2 c1' c2',
    (* presuppositions *)
    wf_lang l ->
    wf_ctxt l c1 c2 ->
    wf_sort l c1 c2 (exp_subst t1 s1) (exp_subst t2 s2) ->
    (* well-formed input *)
    wf_subst l c1 c2 s1 s2 c1' c2' ->
    List.In ({r c1' <# c2' |- e1 <# e2.: t1 <# t2}%rule) l ->
    wf_term l c1 c2 (exp_subst e1 s1) (exp_subst e2 s2) (exp_subst t1 s1) (exp_subst t2 s2)
| wf_term_trans : forall l c1 c2 c3 e1 e2 e3 t1 t2 t3,
    (* presuppositions *)
    wf_lang l ->
    wf_ctxt l c1 c3 ->
    wf_sort l c1 c3 t1 t3 ->
    (* well-formed input *)
    wf_term l c1 c2 e1 e2 t1 t2 ->
    wf_term l c2 c3 e2 e3 t2 t3 ->
    wf_term l c1 c3 e1 e3 t1 t3
(* TODO: these rules are experimental; check *)
| wf_term_conv_r : forall l c1 c2 c3 e1 e2 t1 t2 t3,
    (* presuppositions *)
    wf_lang l ->
    wf_ctxt l c1 c2 ->
    wf_sort l c1 c2 t1 t3 ->
    (* well-formed input *)
    wf_term l c1 c2 e1 e2 t1 t2 ->
    wf_sort l c2 c3 t2 t3 ->
    wf_term l c1 c2 e1 e2 t1 t3
| wf_term_conv_l : forall l c1 c2 c3 e2 e3 t1 t2 t3,
    (* presuppositions *)
    wf_lang l ->
    wf_ctxt l c1 c2 ->
    wf_sort l c1 c2 t1 t3 ->
    (* well-formed input *)
    wf_term l c2 c3 e2 e3 t2 t3 ->
    wf_sort l c1 c2 t1 t2 ->
    wf_term l c1 c2 e2 e3 t1 t3
with wf_subst {p} : lang p ->
                    ctxt p -> ctxt p ->
                    psubst p -> psubst p ->
                    ctxt p -> ctxt p -> Prop :=
| wf_subst_nil : forall l c1 c2 c1' c2',
    (* presuppositions *)
    wf_lang l ->
    (* well-formed input *)
    wf_ctxt l c1 c2 ->
    wf_ctxt l c1' c2' ->
    wf_subst l c1 c2 [::] [::] c1' c2'
| wf_subst_cons_sort : forall l c1 c2 s1 s2 c1' c2' t1 t2,
    (* presuppositions *)
    wf_lang l ->
    wf_ctxt l c1 c2 ->
    wf_ctxt l (sort_var::c1') (sort_var::c2') ->
    (* well-formed input *)
    wf_subst l c1 c2 s1 s2 c1' c2' ->
    wf_sort l c1 c2 t1 t2 ->
    wf_subst l c1 c2 (t1::s1) (t2::s2) (sort_var::c1') (sort_var::c2')
| wf_subst_cons_term : forall l c1 c2 s1 s2 c1' c2' e1 e2 t1 t2,
    (* presuppositions *)
    wf_lang l ->
    wf_ctxt l c1 c2 ->
    wf_ctxt l (term_var t1::c1') (term_var t2::c2') ->
    (* well-formed input *)
    wf_subst l c1 c2 s1 s2 c1' c2' ->
    wf_term l c1 c2 e1 e2 t1 t2 ->
    wf_subst l c1 c2 (e1::s1) (e2::s2) (term_var t1::c1') (term_var t2::c2')
with wf_ctxt_var {p} : lang p -> ctxt p -> ctxt p -> ctxt_var p -> ctxt_var p -> Prop :=
| wf_sort_var : forall l c1 c2,
    (* presuppositions *)
    wf_lang l ->
    (* well-formed input *)
    wf_ctxt l c1 c2 ->
    wf_ctxt_var l c1 c2 sort_var sort_var
| wf_term_var : forall l c1 c2 t1 t2,
    (* presuppositions *)
    wf_lang l ->
    (* well-formed input *)
    wf_sort l c1 c2 t1 t2 ->
    wf_ctxt_var l c1 c2 (term_var t1) (term_var t2)
with wf_ctxt {p} : lang p -> ctxt p -> ctxt p -> Prop :=
| wf_ctxt_nil : forall l, wf_lang l -> wf_ctxt l [::] [::]
| wf_ctxt_cons : forall l c1 c2 v1 v2,
    (* presuppositions *)
    wf_lang l ->
    wf_ctxt l c1 c2 ->
    (* well-formed input *)
    wf_ctxt_var l c1 c2 v1 v2 ->
    wf_ctxt l (v1::c1) (v2::c2)
with wf_rule {p} : lang p -> rule p -> Prop :=
| wf_sort_rule : forall l c1 c2 t1 t2,
    (* presuppositions *)
    wf_lang l ->
    (* well-formed input *)
    wf_ctxt l c1 c2 ->
    wf_rule l ({r c1 <# c2 |- t1 <# t2})
| wf_term_rule : forall l c1 c2 e1 e2 t1 t2,
    (* presuppositions *)
    wf_lang l ->
    wf_ctxt l c1 c2 ->
    (* well-formed input *)
    wf_sort l c1 c2 t1 t2 ->
    wf_rule l ({r c1 <# c2 |- e1 <# e2 .: t1 <# t2})
(* TODO: I make common use of this dependent list structure. Codify?*)
with wf_lang {p} : lang p -> Prop :=
| wf_lang_nil : wf_lang [::]
| wf_lang_cons : forall l r,
    (* presuppositions *)
    wf_lang l ->
    (* well-formed input *)
    wf_rule l r ->
    wf_lang (r::l).

(* well-typed sorts, terms are the reflexive case *)
Definition wf_sort' p l c s : Prop := @wf_sort p l c c s s.
Definition wf_term' p l c e s : Prop := @wf_term p l c c e e s s.
Definition wf_subst' p l c s c' : Prop := @wf_subst p l c c s s c' c'.
Definition wf_ctxt' p l c : Prop := @wf_ctxt p l c c.

Create HintDb wf_hints discriminated.

(* well-formed language suppositions *)
Lemma wf_ctxt_lang  {p} (l : lang p) c1 c2
      (wfc : wf_ctxt l c1 c2) : wf_lang l.
  case: wfc => //=.
Qed.
Hint Immediate wf_ctxt_lang : wf_hints.
Lemma wf_ctxt_var_lang  {p} (l : lang p) c1 c2 v1 v2
           (wf : wf_ctxt_var l c1 c2 v1 v2) : wf_lang l.
  case: wf => //=.
Qed.
Hint Immediate wf_ctxt_var_lang : wf_hints.
Lemma wf_sort_lang  {p} (l : lang p) c1 c2 t1 t2
           (wf : wf_sort l c1 c2 t1 t2) : wf_lang l.
  case: wf => //=.
Qed.
Hint Immediate wf_sort_lang : wf_hints.
Lemma wf_term_lang  {p} (l : lang p) c1 c2 e1 e2 t1 t2
           (wf : wf_term l c1 c2 e1 e2 t1 t2) : wf_lang l.
  case: wf => //=.
Qed.
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
Lemma wf_sort_ctxt  {p} (l : lang p) c1 c2 t1 t2
           (wf : wf_sort l c1 c2 t1 t2) : wf_ctxt l c1 c2.
  case: wf => //=.
Qed.
Hint Immediate wf_sort_ctxt : wf_hints.
Lemma wf_ctxt_var_ctxt  {p} (l : lang p) c1 c2 v1 v2
           (wf : wf_ctxt_var l c1 c2 v1 v2) : wf_ctxt l c1 c2.
  case: wf => //= l' c1' c2' t1 t2 _ /wf_sort_ctxt //=.
Qed.
Hint Immediate wf_ctxt_var_ctxt : wf_hints.
Lemma wf_term_ctxt  {p} (l : lang p) c1 c2 e1 e2 t1 t2
           (wf : wf_term l c1 c2 e1 e2 t1 t2) : wf_ctxt l c1 c2.
  case: wf => //=.
Qed.
Hint Immediate wf_term_ctxt : wf_hints.
Lemma wf_subst_ctxt  {p} (l : lang p) c1 c2 s1 s2 c1' c2'
           (wf : wf_subst l c1 c2 s1 s2 c1' c2') : wf_ctxt l c1 c2.
  case: wf => //=.
Qed.
Hint Immediate wf_subst_ctxt : wf_hints.
Lemma wf_subst_ctxt_out  {p} (l : lang p) c1 c2 s1 s2 c1' c2'
           (wf : wf_subst l c1 c2 s1 s2 c1' c2') : wf_ctxt l c1' c2'.
  case: wf => //=.
Qed.
Hint Immediate wf_subst_ctxt_out : wf_hints.

(* well-formed sort presuppositions *)
Lemma wf_term_sort {p} (l : lang p) c1 c2 e1 e2 t1 t2
           (wf : wf_term l c1 c2 e1 e2 t1 t2) : wf_sort l c1 c2 t1 t2.
  case: wf => //=.
Qed.
Hint Immediate wf_term_sort : wf_hints.

(*
Lemma list_triple_ind {A : Type} (P : seq A -> seq A -> seq A -> Prop)
      (Peee : P [::] [::] [::])
      (Pccc : forall a1 a2 a3 l1 l2 l3, P l1 l2 l3 -> P (a1::l1) (a2::l2) (a3::l3))
      (l1 l2 l3 : seq A)
  : size l1 == size l2 -> size l2 == size l3 -> P l1 l2 l3.
Proof.
    elim: l1 l2 l3.
    - elim => //=; elim => //=.
    - move => a1' l1' IH1.
      elim => //= => a2' l2' IH2.
      elim => //= => a3' l3' IH3 sz12 sz23.
      apply Pccc.
      apply: IH1.
      move: eqSS sz12 => -> //=.
      move: eqSS sz23 => -> //=.
Qed.
Arguments list_triple_ind {A} P Peee Pccc l1 l2 l3.

Fixpoint wf_ctxt_size {p} (l : lang p) c1 c2 (wfc : wf_ctxt l c1 c2) : size c1 == size c2.
Proof.
  elim: wfc => //= l' c1' c2' v1 v2.
Qed.
*)

(* TODO: what is the best way to handle these tactics?
   I am going to want to improve them later, but dont want to rewrite all of them.
   I'm attempting the hint database now. It's possible the tactics won't be necessary?
*)

Variant wf_ctxt_ {p} (l : lang p) : ctxt p -> ctxt p -> Prop :=
| wf_ctxt_nil_ : wf_lang l -> wf_ctxt_ l [::] [::]
| wf_ctxt_cons_ : forall c1 c2 v1 v2,
    wf_ctxt_var l c1 c2 v1 v2 ->
    wf_ctxt_ l (v1::c1) (v2::c2).
Hint Constructors wf_ctxt_.

Variant wf_ctxt_var_ {p} (l : lang p) (c1 c2 : ctxt p) : ctxt_var p -> ctxt_var p -> Prop :=
| wf_sort_var_ : wf_ctxt l c1 c2 -> wf_ctxt_var_ l c1 c2 sort_var sort_var
| wf_term_var_ : forall t1 t2,
    wf_sort l c1 c2 t1 t2 ->
    wf_ctxt_var_ l c1 c2 (term_var t1) (term_var t2).
Hint Constructors wf_ctxt_var_.

Variant wf_sort_ {p} (l : lang p) (c1 c2 : ctxt p) : poly_fix p -> poly_fix p -> Prop :=
| wf_sort_by_ : forall t1 t2 s1 s2 c1' c2',
    wf_sort l c1 c2 t1 t2 ->
    wf_subst l c1 c2 s1 s2 c1' c2' ->
    List.In ({r c1' <# c2'|- t1 <# t2}%rule) l ->
    wf_sort_ l c1 c2 (exp_subst t1 s1) (exp_subst t2 s2)
| wf_sort_trans_ : forall c12 t1 t12 t2,
    (* well-formed input *)
    wf_sort l c1 c12 t1 t12 ->
    wf_sort l c12 c2 t12 t2 ->
    wf_sort_ l c1 c2 t1 t2.
Hint Constructors wf_sort_.

Ltac hypothesize :=
  try match goal with
        [|- _ -> _] => let H := fresh in move => H; hypothesize
      end.

Ltac solve_wf_lang :=
  match goal with
  | [H : wf_ctxt ?l _ _ |- wf_lang ?l] => apply: wf_ctxt_lang; exact H
  | [H : wf_ctxt_var ?l _ _ _ _ |- wf_lang ?l] => apply: wf_ctxt_var_lang; exact H
  | [H : wf_sort ?l _ _ _ _ |- wf_lang ?l] => apply: wf_sort_lang; exact H
  | [H : wf_term ?l _ _ _ _ _ _ |- wf_lang ?l] => apply: wf_term_lang; exact H
  | [H : wf_subst ?l _ _ _ _ _ _ |- wf_lang ?l] => apply: wf_subst_lang; exact H
  | [H : wf_rule ?l _ |- wf_lang ?l] => apply: wf_rule_lang; exact H
  end.

Ltac solve_wf_ctxt :=
  match goal with
  | [H : wf_ctxt_var ?l ?c1 ?c2 _ _ |- wf_ctxt ?l ?c1 ?c2] => apply: wf_ctxt_var_ctxt; exact H
  | [H : wf_sort ?l ?c1 ?c2 _ _ |- wf_ctxt ?l ?c1 ?c2] => apply: wf_sort_ctxt; exact H
  | [H : wf_term ?l ?c1 ?c2 _ _ _ _ |- wf_ctxt ?l ?c1 ?c2] => apply: wf_term_ctxt; exact H
  | [H : wf_subst ?l ?c1 ?c2 _ _ _ _ |- wf_ctxt ?l ?c1 ?c2] => apply: wf_subst_ctxt; exact H
  | [H : wf_subst ?l _ _ _ _ ?c1 ?c2 |- wf_ctxt ?l ?c1 ?c2] => apply: wf_subst_ctxt_out; exact H
  end.

Ltac constr_wf :=
  apply: wf_sort_by
    + apply: wf_sort_trans
    + apply: wf_ctxt_nil
    + apply: wf_ctxt_cons
    + apply: wf_sort_var
    + apply: wf_term_var
    (* good variants *)
    + apply: wf_ctxt_nil_
    + apply: wf_ctxt_cons_
    + apply: wf_sort_by_
    + apply: wf_sort_trans_
    + apply: wf_sort_var_
    + apply: wf_term_var_
             + idtac. 
  
Ltac solve_wf :=
  by hypothesize;
  constr_wf;
  do [solve_wf_lang
     | solve_wf_ctxt
     | eauto].
  
Lemma wf_ctxt_conv p (l : lang p) c1 c2 : wf_ctxt l c1 c2 <-> wf_ctxt_ l c1 c2.
Proof.
  split; case; solve_wf.
Qed.
Hint Resolve <- wf_ctxt_conv 0 : wf_hints.
Coercion ctxt_coerce p (l : lang p) c1 c2 := fst (wf_ctxt_conv l c1 c2).

Lemma wf_ctxt_var_conv p (l : lang p) c1 c2 v1 v2
  : wf_ctxt_var l c1 c2 v1 v2 <-> wf_ctxt_var_ l c1 c2 v1 v2.
Proof.
  split; case; solve_wf.
Qed.
Hint Resolve <- wf_ctxt_var_conv 0 : wf_hints.
Coercion ctxt_var_coerce p (l : lang p) c1 c2 v1 v2 := fst (wf_ctxt_var_conv l c1 c2 v1 v2).

Fixpoint wf_ctxt_to_trans' (n : nat) p (l : lang p) (c1 c2 c3 :ctxt p) {struct n}
  : n = 2 * size c1 -> wf_ctxt l c1 c2 -> wf_ctxt l c2 c3 -> wf_ctxt l c1 c3
with wf_ctxt_var_to_trans' (n : nat) p (l : lang p) c1 c2 c3 v1 v2 v3 {struct n}
     : n = (2 * size c1).+1 ->
       wf_ctxt_var l c1 c2 v1 v2 ->
       wf_ctxt_var l c2 c3 v2 v3 ->
       wf_ctxt_var l c1 c3 v1 v3.
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
      apply wf_ctxt_conv;
      constructor => //=.
      rewrite -H4 in wf2;
        inversion wf2.
      apply wf_ctxt_conv;
        constructor => //=.
      apply: (wf_ctxt_var_to_trans' n0) => //=.
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
        apply wf_ctxt_var_conv;
        constructor.
      * apply: (wf_ctxt_to_trans' n0) => //=.        
        exact H1.
        done.
      * have wfs13 : wf_sort l c1 c3 t1 t3.
        apply: wf_sort_trans.
        done.
        apply: (wf_ctxt_to_trans' n0) => //=.
        apply: wf_sort_ctxt; eauto.
        apply: wf_sort_ctxt; eauto.
        eauto.
        eauto.
        done.
Qed. 


Lemma wf_ctxt_to_trans p (l : lang p) (c1 c2 c3 :ctxt p)
  : wf_ctxt l c1 c2 -> wf_ctxt l c2 c3 -> wf_ctxt l c1 c3.
Proof.
  apply: wf_ctxt_to_trans' => //=.
Qed.
                                                        
Lemma wf_ctxt_var_to_trans p (l : lang p) c1 c2 c3 v1 v2 v3
     : wf_ctxt_var l c1 c2 v1 v2 ->
       wf_ctxt_var l c2 c3 v2 v3 ->
       wf_ctxt_var l c1 c3 v1 v3.
Proof.
  apply: wf_ctxt_var_to_trans'; eauto.
Qed.



Fail Define fls := 0.

  Inductive wf_sort {p} : lang p -> ctxt p -> ctxt p -> poly_fix p -> poly_fix p -> Prop :=
| wf_sort_trans : forall l c1 c2 c3 t1 t2 t3,
    (* presuppositions *)
    wf_lang l ->
    wf_ctxt l c1 c3 ->
    (* well-formed input *)
    wf_sort l c1 c2 t1 t2 ->
    wf_sort l c2 c3 t2 t3 ->
    wf_sort l c1 c3 t1 t3
with wf_term {p} : lang p ->
                   ctxt p -> ctxt p ->
                   poly_fix p -> poly_fix p ->
                   poly_fix p -> poly_fix p -> Prop :=
| wf_term_by : forall l c1 c2 e1 e2 t1 t2 s1 s2 c1' c2',
    (* presuppositions *)
    wf_lang l ->
    wf_ctxt l c1 c2 ->
    wf_sort l c1 c2 (exp_subst t1 s1) (exp_subst t2 s2) ->
    (* well-formed input *)
    wf_subst l c1 c2 s1 s2 c1' c2' ->
    List.In ({r c1' <# c2' |- e1 <# e2.: t1 <# t2}%rule) l ->
    wf_term l c1 c2 (exp_subst e1 s1) (exp_subst e2 s2) (exp_subst t1 s1) (exp_subst t2 s2)
| wf_term_trans : forall l c1 c2 c3 e1 e2 e3 t1 t2 t3,
    (* presuppositions *)
    wf_lang l ->
    wf_ctxt l c1 c3 ->
    wf_sort l c1 c3 t1 t3 ->
    (* well-formed input *)
    wf_term l c1 c2 e1 e2 t1 t2 ->
    wf_term l c2 c3 e2 e3 t2 t3 ->
    wf_term l c1 c3 e1 e3 t1 t3
(* TODO: these rules are experimental; check *)
| wf_term_conv_r : forall l c1 c2 c3 e1 e2 t1 t2 t3,
    (* presuppositions *)
    wf_lang l ->
    wf_ctxt l c1 c2 ->
    wf_sort l c1 c2 t1 t3 ->
    (* well-formed input *)
    wf_term l c1 c2 e1 e2 t1 t2 ->
    wf_sort l c2 c3 t2 t3 ->
    wf_term l c1 c2 e1 e2 t1 t3
| wf_term_conv_l : forall l c1 c2 c3 e2 e3 t1 t2 t3,
    (* presuppositions *)
    wf_lang l ->
    wf_ctxt l c1 c2 ->
    wf_sort l c1 c2 t1 t3 ->
    (* well-formed input *)
    wf_term l c2 c3 e2 e3 t2 t3 ->
    wf_sort l c1 c2 t1 t2 ->
    wf_term l c1 c2 e2 e3 t1 t3
with wf_subst {p} : lang p ->
                    ctxt p -> ctxt p ->
                    psubst p -> psubst p ->
                    ctxt p -> ctxt p -> Prop :=
| wf_subst_nil : forall l c1 c2 c1' c2',
    (* presuppositions *)
    wf_lang l ->
    (* well-formed input *)
    wf_ctxt l c1 c2 ->
    wf_ctxt l c1' c2' ->
    wf_subst l c1 c2 [::] [::] c1' c2'
| wf_subst_cons_sort : forall l c1 c2 s1 s2 c1' c2' t1 t2,
    (* presuppositions *)
    wf_lang l ->
    wf_ctxt l c1 c2 ->
    wf_ctxt l (sort_var::c1') (sort_var::c2') ->
    (* well-formed input *)
    wf_subst l c1 c2 s1 s2 c1' c2' ->
    wf_sort l c1 c2 t1 t2 ->
    wf_subst l c1 c2 (t1::s1) (t2::s2) (sort_var::c1') (sort_var::c2')
| wf_subst_cons_term : forall l c1 c2 s1 s2 c1' c2' e1 e2 t1 t2,
    (* presuppositions *)
    wf_lang l ->
    wf_ctxt l c1 c2 ->
    wf_ctxt l (term_var t1::c1') (term_var t2::c2') ->
    (* well-formed input *)
    wf_subst l c1 c2 s1 s2 c1' c2' ->
    wf_term l c1 c2 e1 e2 t1 t2 ->
    wf_subst l c1 c2 (e1::s1) (e2::s2) (term_var t1::c1') (term_var t2::c2')
with wf_ctxt_var {p} : lang p -> ctxt p -> ctxt p -> ctxt_var p -> ctxt_var p -> Prop :=
| wf_sort_var : forall l c1 c2,
    (* presuppositions *)
    wf_lang l ->
    (* well-formed input *)
    wf_ctxt l c1 c2 ->
    wf_ctxt_var l c1 c2 sort_var sort_var
| wf_term_var : forall l c1 c2 t1 t2,
    (* presuppositions *)
    wf_lang l ->
    (* well-formed input *)
    wf_sort l c1 c2 t1 t2 ->
    wf_ctxt_var l c1 c2 (term_var t1) (term_var t2)
with wf_ctxt {p} : lang p -> ctxt p -> ctxt p -> Prop :=
| wf_ctxt_nil : forall l, wf_lang l -> wf_ctxt l [::] [::]
| wf_ctxt_cons : forall l c1 c2 v1 v2,
    (* presuppositions *)
    wf_lang l ->
    wf_ctxt l c1 c2 ->
    (* well-formed input *)
    wf_ctxt_var l c1 c2 v1 v2 ->
    wf_ctxt l (v1::c1) (v2::c2)
with wf_rule {p} : lang p -> rule p -> Prop :=
| wf_sort_rule : forall l c1 c2 t1 t2,
    (* presuppositions *)
    wf_lang l ->
    (* well-formed input *)
    wf_ctxt l c1 c2 ->
    wf_rule l ({r c1 <# c2 |- t1 <# t2})
| wf_term_rule : forall l c1 c2 e1 e2 t1 t2,
    (* presuppositions *)
    wf_lang l ->
    wf_ctxt l c1 c2 ->
    (* well-formed input *)
    wf_sort l c1 c2 t1 t2 ->
    wf_rule l ({r c1 <# c2 |- e1 <# e2 .: t1 <# t2})
(* TODO: I make common use of this dependent list structure. Codify?*)
with wf_lang {p} : lang p -> Prop :=
| wf_lang_nil : wf_lang [::]
| wf_lang_cons : forall l r,
    (* presuppositions *)
    wf_lang l ->
    (* well-formed input *)
    wf_rule l r ->
    wf_lang (r::l).


  (*TODOTODOTODO: old*)

  Fixpoint wf_ctxt_lang {p} (l : lang p) c1 c2
           (wfc : wf_ctxt l c1 c2) : wf_lang l :=
    match wfc with
    | wf_ctxt_nil l' pf => pf
    | wf_ctxt_cons l' c1' c2' v1 v2 wfv => wf_ctxt_var_lang wfv
    end
  with wf_ctxt_var_lang {p} (l : lang p) c1 c2 v1 v2
                        (wfv : wf_ctxt_var l c1 c2 v1 v2) : wf_lang l :=
         match wfv with
         | wf_sort_var l c1 c2 wfc => wf_ctxt_lang wfc
         | wf_term_var l c1 c2 t1 t2 wfs => wf_sort_lang wfs
         end
  with wf_sort_lang {p} (l : lang p) c1 c2 t1 t2
                    (wfs : wf_sort l c1 c2 t1 t2) : wf_lang l :=
         match wfs with
         | wf_sort_by l c1 c2 t1 t2 s1 s2 c1' c2' wfsb _ =>
           wf_subst_lang wfsb
         | wf_sort_trans l c1 c2 c3 t1 t2 t3 wfs1 _ => wf_sort_lang wfs1
         end
  with wf_subst_lang {p} (l : lang p) c1 c2 s1 s2 c1' c2'
                     (wfsb : wf_subst l c1 c2 s1 s2 c1' c2') : wf_lang l :=
         match wfsb with
         | wf_subst_nil l c1 c2 c1' c2' wfc => wf_ctxt_lang wfc
         | wf_subst_cons_sort l c1 c2 s1 s2 c1' c2' _ _ wfsb _ 
         | wf_subst_cons_term l c1 c2 s1 s2 c1' c2' _ _ _ _ wfsb _ =>
           wf_subst_lang wfsb
         end.

  Fixpoint wf_term_lang {p} (l : lang p) c1 c2 e1 e2 t1 t2
           (wft : wf_term l c1 c2 e1 e2 t1 t2) : wf_lang l :=
    match wft with
    | wf_term_by  l c1 c2 e1 e2 t1 t2 s1 s2 c1' c2' wfsb _ => wf_subst_lang wfsb
    | wf_term_trans l c1 c2 c3 e1 e2 e3 t1 t2 t3 wft1 _ => wf_term_lang wft1
    | wf_term_conv_r l c1 c2 c3 e1 e2 t1 t2 t3 _ wfs => wf_sort_lang wfs
    | wf_term_conv_l l c1 c2 c3 e2 e3 t1 t2 t3 _ wfs => wf_sort_lang wfs
    end.


    
  
  Lemma wf_ctxt_trans {p} (l : lang p) c1 c2 c3
        (wfc1 : wf_ctxt l c1 c2) (wfc2 : wf_ctxt l c2 c3) : wf_ctxt l c1 c3.
  Proof.
    
  elim: wfc1 wfc2 => //=.
  move => l' c1' c2' v1 v2 wfv wfc.
  have c3c : ~c3 = [::];
    [by inversion wfc|..].
  elim: wfc.
  elim: c3 => [wfc|]; [inversion wfc|].
  move => v3 c3'.
  
  (* TODO: relies on ctxt transitivity *)
  Fixpoint wf_sort_ctxt {p} (l : lang p) c1 c2 t1 t2
           (wfs : wf_sort l c1 c2 t1 t2) : wf_ctxt l c1 c2 :=
    match wfs with
    | wf_sort_by l c1 c2 t1 t2 s1 s2 c1' c2' wfsb _ =>
      wf_subst_ctxt wfsb
    end
  with wf_subst_ctxt {p} (l : lang p) c1 c2 s1 s2 c1' c2'
                     (wfsb : wf_subst l c1 c2 s1 s2 c1' c2') :=
         match wfsb with
         | wf_subst_nil l c1 c2 c1' c2' wfc => wfc
         | wf_subst_cons_sort l c1 c2 s1 s2 c1' c2' _ _ wfsb _ 
         | wf_subst_cons_term l c1 c2 s1 s2 c1' c2' _ _ _ _ wfsb _ =>
           wf_subst_ctxt wfsb
         end.

  
  Fixpoint wf_term_ctxt {p} (l : lang p) c1 c2 e1 e2 t1 t2
        (wft : wf_term l c1 c2 e1 e2 t1 t2) : wf_ctxt l c1 c2 :=
    match wft with
    | wf_term_by  l c1 c2 e1 e2 t1 t2 s1 s2 c1' c2' wfsb _ => wf_subst_ctxt wfsb
    | wf_term_conv_r l c1 c2 c3 e1 e2 t1 t2 t3 wft wfs =>
      wf_ctxt_trans (wf_term_ctxt wft) (wf_sort_ctxt wfs)
    | wf_term_conv_l l c1 c2 c3 e2 e3 t1 t2 t3 wft wfs =>
      wf_ctxt_trans (wf_sort_ctxt wfs) (wf_term_ctxt wft)
    end.
  

  Definition wfs_le {p} l (s1 s2 : wft l) : Prop :=
    match s1, s2 with
    ...
  
  Lemma sort_le_refl {p} l : forall s : wft l, 
  
  (* Sort and term relations are reflexive trivially *)

  
  Lemma le_sort_trans {p} (l : lang p) c1 c2 
  
  
End LangProps.



(* TODOTODOTODOTOOTODOTODOTODOTODOTODO:
   preorder type theory! necessary to model weakening the way I want
   TODO: If I do preorder type theory, can/should I simplify to only precision judgments?
*)
