
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
  
Definition sort_rule p : Type := ctxt p * poly_fix p.
  
Definition term_rule p : Type := ctxt p * poly_fix p * poly_fix p.

(* terms form a category over sorts w/ (empty or constant?) Γ *)
(* TODO: two ctxts? *)
Definition sort_le_rule p : Type := (ctxt p * ctxt p) * (poly_fix p * poly_fix p).

Definition term_le_rule p : Type :=
  (ctxt p * ctxt p) * (poly_fix p * poly_fix p) * (poly_fix p * poly_fix p).

(* TODO: inline all of these defs? probably not? *)
Inductive rule (p : polynomial) : Type :=
| sort : sort_rule p -> rule p
| term : term_rule p -> rule p
| sort_le : sort_le_rule p -> rule p
| term_le : term_le_rule p -> rule p.

Notation "{ c1 <# c2 |- s1 <# s2 }" := (sort_le ((c1,c2), (s1, s2))) (at level 80).
Notation "{ c1 <# c2 |- e1 <# e2 .: s1 <# s2 }" :=
  (term_le ((c1,c2), (e1,e2), (s1, s2))) (at level 80).
Notation "{ c |- s1 <# s2 }" := (sort_le ((c,c), (s1, s2))) (at level 80).
Notation "{ c |- e1 <# e2 .: s1 <# s2 }" := (term_le ((c,c), (e1,e2), (s1, s2))) (at level 80).
Notation "{ c |- e1 <# e2 .: s }" := (term_le ((c,c), (e1,e2), (s, s))) (at level 80).

Definition lang p := list (rule p).
  
(* syntax of single explicit substitutions *)
Definition subst_syn : polynomial :=
  [:: (nat, 0); (* var (deBruijn) *)
     (unit, 2) (*subst M[N/0] *)
  ].

Definition wf_sort_and_cong {p : polynomial} (wfs : sort_rule p) : lang p :=
  let (c, s) := wfs in
  [:: {c |- s <# s}; sort wfs].

Definition wf_term_and_cong {p : polynomial} (wft : term_rule p) : lang p :=
  let (ct, s) := wft in
  let (c, t) := ct in
  [::  {c |- t <# t .: s}; term wft].


Definition sub (m n : poly_fix subst_syn) : poly_fix subst_syn :=
  [{subst_syn} 1 | tt , [* m; n]].

Definition svar (n : nat) : poly_fix subst_syn :=
  [{subst_syn} 0 | n , [*]].

  (* equational theory of substitutions *)
Definition subst_lang : lang subst_syn :=
  [:: { [:: sort_var] |- sub (svar 0) (var 0) <# var 0}]
    ++ (List.flat_map
     wf_sort_and_cong
     [:: ([:: sort_var; sort_var],
          [{subst_syn} 1 | tt, [* var 0; var 1]]);
        ([:: sort_var; sort_var; term_var (var 1)],
         [{subst_syn} 1 | tt , [* var 0; var 2]])])
    ++ (List.flat_map
          wf_term_and_cong
          [:: ([:: sort_var; term_var (var 0); sort_var ],
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
  | {c1 <# c2 |- s1 <# s2} :: l' => ws_lang l' && ws_exp (size c1) s1 && ws_exp (size c2) s2
  | {c1 <# c2 |- e1 <# e2 .: s1 <# s2} :: l' =>
    ws_lang l' && ws_exp (size c1) e1 && ws_exp (size c2) e2
            && ws_exp (size c1) s1 && ws_exp (size c2) s2
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
(* We could embed well-scopedness in bool, but well-typedness can be undecideable,
   so we leave it in Prop.
   All judgements presuppose that the input language is well-formed to be sensible.
   TODO: should I try to avoid mutual induction?/build in these presuppositions?
 *)
(* TODO: make clear & clean admissible vs derivable props *)
(* TODO: include language equality (will change most defs) *)
Inductive wf_sort {p} : lang p -> ctxt p -> poly_fix p -> Prop :=
| wf_sort_by : forall l c e s c',
    (* these should be admissible
       wf_lang l ->
       wf_ctxt l c -> 
       wf_ctxt l c' -> 
       wf_sort l c' e *)
    wf_subst l c s c' ->
    List.In (sort (c',e)) l ->
    wf_sort l c (exp_subst e s)
with wf_sort_le {p} : lang p -> ctxt p -> ctxt p -> poly_fix p -> poly_fix p -> Prop :=
| wf_sort_le_by : forall l c1 c2 t1 t2 s1 s2 c1' c2',
    (* these should be admissible
       wf_lang l ->
       wf_ctxt l c -> 
       wf_ctxt l c' -> 
       wf_sort l c' t1 -> 
       wf_sort l c' t2 -> *)
    wf_subst l c1 s1 c1' ->
    wf_subst l c2 s2 c2' ->
    (*todo: subst le*)
    List.In ({c1' <# c2'|- t1 <# t2}) l ->
    wf_sort_le l c1 c2 (exp_subst t1 s1) (exp_subst t2 s2)
with  wf_term {p} : lang p -> ctxt p -> poly_fix p -> poly_fix p -> Prop :=
| wf_term_by : forall l c e t s c',
    (* these should be admissible
       wf_lang l ->
       wf_ctxt l c -> 
       wf_ctxt l c' -> 
       wf_term l c' e t *)
    wf_subst l c s c' ->
    List.In (term (c',e,t)) l ->
    wf_term l c (exp_subst e s) (exp_subst t s)
with wf_subst {p} : lang p -> ctxt p -> psubst p -> ctxt p -> Prop :=
| wf_subst_nil : forall l c c',
    (* wf_lang l ->*)
    wf_ctxt l c ->
    wf_ctxt l c' ->
    wf_subst l c [::] c'
| wf_subst_cons_sort : forall l c s c' e,
    (* wf_lang l ->
       wf_ctxt l c ->
       wf_ctxt l c' ->*)
    wf_subst l c s c' ->
    wf_sort l c e ->
    wf_subst l c (e::s) (sort_var::c')
| wf_subst_cons_term : forall l c s c' e t,
    (* wf_lang l ->
       wf_ctxt l c ->
       wf_ctxt l c' ->*)
    wf_subst l c s c' ->
    wf_term l c e t ->
    wf_subst l c (e::s) (term_var t::c')
with wf_subst_le {p} : lang p ->
                       ctxt p -> ctxt p ->
                       psubst p -> psubst p ->
                       ctxt p -> ctxt p -> Prop :=
| wf_subst_le_nil : forall l c1 c2 c1' c2',
    (* wf_lang l ->*)
    wf_ctxt l c1 ->
    wf_ctxt l c1' ->
    wf_subst_le l c1 c2 [::] [::] c1' c2'
| wf_subst_le_cons_sort : forall l c s c' e,
    (* wf_lang l ->
       wf_ctxt l c ->
       wf_ctxt l c' ->*)
    wf_subst l c s c' ->
    wf_sort l c e ->
    wf_subst_le l c (e::s) (sort_var::c')
| wf_subst_le_cons_term : forall l c s c' e t,
    (* wf_lang l ->
       wf_ctxt l c ->
       wf_ctxt l c' ->*)
    wf_subst l c s c' ->
    wf_term l c e t ->
    wf_subst_le l c (e::s) (term_var t::c')
with wf_ctxt_var {p} : lang p -> ctxt p -> ctxt_var p -> Prop :=
| wf_sort_var : forall l c,
    (* wf_lang l ->*)
    wf_ctxt l c ->
    wf_ctxt_var l c sort_var
| wf_term_var : forall l c t,
    (*wf_lang l ->*)
    wf_sort l c t ->
    wf_ctxt_var l c (term_var t)
with wf_ctxt {p} : lang p -> ctxt p -> Prop :=
| wf_ctxt_nil : forall l, wf_lang l -> wf_ctxt l [::]
| wf_ctxt_cons : forall l c v,
    (*wf_lang l ->*)
    (*wf_ctxt l c ->*)
    wf_ctxt_var l c v -> wf_ctxt l (v::c)
with wf_rule {p} : lang p -> rule p -> Prop :=
| wf_sort_rule : forall l c t,
    (*wf_lang l ->*)
    wf_ctxt l c ->
    ws_exp (size c) t ->
    wf_rule l (sort (c,t))
| wf_term_rule : forall l c e t,
    (*wf_lang l ->*)
    (*wf_ctxt l c ->*)
    wf_sort l c t ->
    ws_exp (size c) e ->
    wf_rule l (term (c,e,t))
| wf_sort_eq_rule : forall l c1 c2 t1 t2,
    (*wf_lang l ->*)
    (*wf_ctxt l c ->*)
    (*wf_ctxt_le l c -> TODO*)
    wf_sort l c1 t1 ->
    wf_sort l c2 t2 ->
    wf_rule l ({ c1 <# c2 |- t1 <# t2})
| wf_term_eq_rule : forall l c1 c2 e1 e2 t1 t2,
    (*wf_lang l ->*)
    (*wf_ctxt l c ->*)
    (*wf_sort l c t->*)
    wf_term l c1 e1 t1 ->
    wf_term l c2 e2 t2 ->
    wf_rule l ({ c1 <# c2 |- e1 <# e2 .: t1 <# t2})
(* TODO: I make common use of this dependent list structure. Codify?*)
with wf_lang {p} : lang p -> Prop :=
| wf_lang_nil : wf_lang [::]
| wf_lang_cons : forall l r, wf_lang l -> wf_rule l r -> wf_lang (r::l).


(* TODOTODOTODOTOOTODOTODOTODOTODOTODO:
   preorder type theory! necessary to model weakening the way I want
   TODO: If I do preorder type theory, can/should I simplify to only precision judgments?
*)
