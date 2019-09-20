
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
 *)

Inductive ws_exp {p : polynomial} (c : ctxt p) : poly_fix p -> Prop :=
| ws_var : forall n, n < size c -> ws_exp c (var n)
| ws_con : forall n s v, Vector.Forall (ws_exp c) v -> ws_exp c (con n s v).

Definition ws_ctxt_var {p : polynomial} (c : ctxt p) (v : ctxt_var p) : Prop :=
  match v with
  | sort_var => True
  | term_var ty => ws_exp c ty
  end.
Fixpoint ws_ctxt {p : polynomial} (c : ctxt p) : Prop :=
  match c with
  | [::] => True
  | v :: c' => ws_ctxt c' /\ ws_ctxt_var c' v
  end.
Fixpoint ws_lang {p : polynomial} (l : lang p) : Prop :=
  match l with
  |[::] => True
  | sort (c, s) :: l' => ws_lang l' /\ ws_ctxt c /\ ws_exp c s
  | term (c, t, s) :: l' => ws_lang l' /\ ws_ctxt c /\ ws_exp c t /\ ws_exp c s
  | sort_eq (c, (s1,s2)) :: l' => ws_lang l' /\ ws_exp c s1 /\ ws_exp c s2
  | term_eq (c, (t1,t2), s) :: l' => ws_lang l' /\ ws_exp c t1 /\ ws_exp c t2 /\ ws_exp c s
  end.


Definition ws_subst {p} (c : ctxt p) (s : psubst p) : Prop :=
  List.Forall (ws_exp c) s.

Lemma ws_nth : forall p (c : ctxt p) s e n, ws_subst c s -> ws_exp c e -> ws_exp c (nth e s n).
Proof.
  move => p c; elim.
  - move => e; elim; [done|].
    move => n IH //=.
  - move => x l IH e.
    elim => [| n _].
    + case; done.
    + move => wss wse; apply: IH;[inversion wss|]; done.
Qed.

(*TODO: subst doesn't readjust ctxt vars. This approach seems awkward*)
(* Use Fin n for scoping?*)
Theorem subst_preserves_ws
  : forall {p} e s (c : ctxt p),
    ws_exp c e ->
    ws_subst (drop (size s) c) s ->
    ws_exp (drop (size s) c) (exp_subst e s).
Proof.
  move => p e s c.
  elim => [n nlt | n s' v vfa] wse.
  - rewrite /exp_subst lookup_nth.
    apply: ws_nth; [done|].
    (*TODO: need |s| < |c|*)
    apply ws_var.
    rewrite size_drop ltn_sub2r //=.
    
    Check ltn_sub2r.
    rewrite size_drop.
    
    ws_subst c s -> ws_exp c e -> ws_exp c (nth e s n)
    have nmllt : n - size s < size (drop (size s) c).
    rewrite size_drop ltn_sub2r //=.
    
    rewrite <- (cat_take_drop (length s) c) in H.
    rewrite List.app_length in H.
    Search _ ( _ < _ + _).
    Search length.
    Search _ (length (_ ++ _)).
    Search _ ((take _ _) ++ (drop _ _)).
    remember (n < length s) as nlts.
    destruct nlts.
    induction s.
   + rewrite drop0.
     simpl.
     auto.
   + destruct c.
     simpl.
     
     
  
Theorem subst_preserves_ws
  : forall {p} e s (c1 c2 : ctxt p),
    length s = length c1 ->
    ws_exp c1 e ->
    ws_subst c2 s ->
    ws_exp c2 (exp_subst e s).
Proof.
  intros.
  
  move =>.
  elim.
  elim.
  elim.  
  simpl.
  move => c1 c2 lz; destruct c1;[| by inversion lz].
  move => wsz; by inversion wsz.
  move => e s IH.
  

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
