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

Variant sort : Set := scon : string -> list exp -> sort.

Definition ctx : Set := named_list_set sort.

Definition subst : Set := named_list_set exp.

Definition subst_lookup (s : subst) (n : string) : exp :=
  named_list_lookup (var n) s n.

Arguments subst_lookup !s n/.

Definition ctx_lookup (c: ctx) (n : string) : sort :=
  named_list_lookup (scon "" [::]) c n.

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
  match t with scon _ s => ws_args args s end.
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
  let (c, s') := t in scon c s'[/s/].
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


Fixpoint eq_exp e1 e2 {struct e1} : bool :=
  match e1, e2 with
  | var x, var y => eqb x y
  | con n1 l1, con n2 l2 =>
    (eqb n1 n2) && (all2 eq_exp l1 l2)
  | _,_ => false
  end.


Lemma eq_exp_refl : forall e, eq_exp e e.
Proof.
  elim; simpl; auto.
  move => n.
  apply eqb_refl.
  intro n.
  elim; simpl; auto.
  rewrite eqb_refl; auto.
  intro_to and.
  case => eqaa fld.
  apply /andP.
  split; auto.
  apply /eqb_refl.
  move: (H fld) => H'; break; break_goal; auto.
Qed.

Lemma all2_eq_exp_refl : forall l, all2 eq_exp l l.
  pose eqer := eq_exp_refl.
  elim; simpl; auto.
  intros; apply /andP; split; auto.
Qed.


Lemma eq_expP : forall e1 e2, reflect (e1 = e2) (eq_exp e1 e2).
  intro e1.
  induction e1; intro e2; destruct e2; simpl; try by constructor.
  {
    destruct_reflect_bool.
    f_equal; apply /eqP; symmetry; assumption.
    case => /eqP.
    change (?n == ?s) with (n=? s)%string.
    rewrite - Heqb.
    inversion.
  }
  {
    destruct_reflect_andb_l; simpl;
      [|constructor;
        case; intros; subst;
        rewrite eqb_refl in Heqb;
        inversion Heqb ].
    symmetry in Heqb.
    move: Heqb =>/eqP ->.
    suff: (reflect (l=l0) (all2 eq_exp l l0)).
    {
      move => lP; destruct_reflect_bool.
      {
        f_equal.
        by apply /lP.
      }
      {
        case.
        move /lP; inversion.
      }
    }
    {
      clear n s.
      revert l0 X.
      induction l; intro l0; destruct l0; simpl; try by constructor.
      intros; break.
      destruct_reflect_andb_l.
      symmetry in Heqb.
      {
        move: Heqb => /r Heqb; subst; simpl.
        destruct_reflect_bool; [f_equal | inversion].
        {
          symmetry in Heqb.
          move: Heqb => /IHl; auto.
        }
        {
          subst.
          rewrite all2_eq_exp_refl in Heqb.
          inversion Heqb.
        }
      }
      {
        constructor.
        inversion; subst.
        rewrite eq_exp_refl in Heqb.
        inversion Heqb.
      }
    }
  }
Qed.          
     
Definition exp_eqMixin := Equality.Mixin eq_expP.

Canonical exp_eqType := @Equality.Pack exp exp_eqMixin.

Definition eq_sort (t1 t2 : sort) :=
  let (n1, s1) := t1 in
  let (n2, s2) := t2 in
  (n1 == n2) && (s1 == s2).

Lemma eq_sortP s1 s2 : reflect (s1 = s2) (eq_sort s1 s2).
  destruct s1; destruct s2; simpl; solve_reflect_norec.
Qed.

Canonical sort_eqType := @Equality.Pack sort (Equality.Mixin eq_sortP).

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
  by rewrite named_map_fst_eq.
Qed.  

Ltac fold_Substable :=
  try change (named_map (exp_subst ?s') ?s) with s[/s'/];
  try change (exp_subst ?s ?e) with e[/s/];
  try change (sort_subst ?s ?e) with e[/s/];
  try change (args_subst ?s ?e) with e[/s/];
  try change (subst_cmp ?s ?e) with e[/s/];
  try change (map (exp_var_map (subst_lookup ?s')) ?s) with s[/s'/].


Lemma ws_subst_args args (s : subst)
  : well_scoped args s = (all_fresh s) && (well_scoped args (map snd s)).
Proof using .
  elim: s; simpl; auto.
  case; intros n0 e0 s IH; simpl.
  unfold well_scoped in IH; simpl in *.
  rewrite IH.
  ring.
Qed.

Lemma ws_exp_ext_ctx args n (e : exp)
  : well_scoped args e -> well_scoped (n::args) e.
Proof using .
  elim: e.
  {
    intros; simpl in *.
    rewrite in_cons.
    apply /orP; by right.
  }
  {
    intros until l.
    elim: l; intros; simpl in *; break; auto.
    break_goal; auto.
  }
Qed.

Lemma ws_args_ext_ctx args n (l : list exp)
  : well_scoped args l -> well_scoped (n::args) l.
Proof using .
  elim: l; intros; simpl in *; break; auto.
  break_goal; auto using ws_exp_ext_ctx.
Qed.

Lemma ws_sort_ext_ctx args n (e : sort)
  : well_scoped args e -> well_scoped (n::args) e.
Proof using .
  case: e; intros; simpl; auto using ws_args_ext_ctx.
Qed.
    
Lemma sort_in_ws c n t : ws_ctx c -> (n,t) \in c -> ws_sort (map fst c) t.
Proof using .
  elim: c; intros; break; simpl in *; break; auto.
  match goal with [H : is_true(_ \in _::_)|- _]=>
                  move: H;rewrite in_cons; move /orP => [] end.
  {
    move /eqP => []; intros; subst.
    auto using ws_sort_ext_ctx.
  }
  {
    intros.
    auto using ws_sort_ext_ctx.
  }
Qed.

Definition id_subst args : subst := map (fun x => (x,var x)) args.

Lemma id_subst_reduce args (e : exp)
  : e[/id_subst args/] = e.
Proof.
  elim: e.
  {
    intros; cbn.
    elim args.
    { reflexivity. }
    {
      intros; simpl.
      case_match.
      symmetry in HeqH0.
      move: HeqH0 => /eqP -> //=.
      exact H.
    }
  }
  {
    intros; cbn; f_equal.
    elim: l H; simpl; intros; break; f_equal.
    exact H0.
    auto.
  }
Qed.


Lemma id_subst_reduce_sort args (e : sort)
  : e[/id_subst args/] = e.
Proof.
  destruct e.
  intros; cbn; f_equal.
  elim: l; simpl; intros; break; f_equal; eauto using id_subst_reduce.
Qed.

Module Notations.

  Declare Custom Entry exp.
  Declare Custom Entry sort.
  

  Declare Custom Entry ctx.
  Declare Custom Entry ctx_binding.

  (* Since contexts are regular lists, 
     we need a scope to determine when to print them *)
  Declare Scope ctx_scope.
  Bind Scope ctx_scope with ctx.
  
  Notation "'{{e' e }}" := (e) (at level 0,e custom exp at level 100).
  Notation "'{{s' e }}" := (e) (at level 0,e custom sort at level 100).
  
  Notation "{ x }" :=
    x (in custom exp at level 0, x constr).
  Notation "{ x }" :=
    x (in custom sort at level 0, x constr).
  (* TODO: issues; fix *)
  Notation "{ x }" :=
    x (in custom ctx at level 0, x constr).
  
  Notation "# c" :=
    (con c%string [::])
      (right associativity,in custom exp at level 0, c constr at level 0,
                              format "# c").
  Notation "# c" :=
    (scon c%string [::])
      (right associativity,in custom sort at level 0, c constr at level 0,
                              format "# c").

  Definition exp_constr_app e e' :=
    match e with
    | con c l => con c (e'::l)
    | _ => con "ERR" [::]
    end.

  Definition srt_constr_app t e' :=
    match t with
    | scon c l => scon c (e'::l)
    end.

  Notation "c e" :=
    (exp_constr_app c e)
      (left associativity, in custom exp at level 10,
                              c custom exp, e custom exp at level 9).
  Notation "c e" :=
    (srt_constr_app c e)
      (left associativity, in custom sort at level 10,
                              c custom sort, e custom exp at level 9).

  Notation "( e )" := e (in custom exp at level 0, e custom exp at level 100).
  Notation "( e )" := e (in custom sort at level 0, e custom sort at level 100).

  Notation "% x" :=
    (var x%string)
      (in custom exp at level 0, x constr at level 0, format "% x").


  Check {{e #"foo" }}.
  Check {{e #"foo" (#"bar" %"x") #"baz" %"y"}}.
  Check {{s #"foo" }}.
  Check {{s #"foo" (#"bar" %"x") #"baz" %"y"}}.

  
  Eval compute in {{e #"foo" (#"bar" %"x") #"baz" %"y"}}.
  
  Notation "# c e1 .. en"
    := (con c (cons en .. (cons e1 nil) ..))
      (left associativity,
         in custom exp at level 10,
            c constr at level 0,
            e1 custom exp at level 9,
            en custom exp at level 9,
            only printing).

  Notation "# c e1 .. en"
    := (scon c (cons en .. (cons e1 nil) ..))
      (left associativity,
         in custom sort at level 10,
            c constr at level 0,
            e1 custom exp at level 9,
            en custom exp at level 9,
            only printing).
  
  Eval compute in {{e #"foo" (#"bar" %"x") #"baz" %"y"}}.
  Eval compute in {{s #"foo" (#"bar" %"x") #"baz" %"y"}}.
  Eval compute in {{s #"foo" }}.
                               
  Bind Scope ctx_scope with ctx.

  Notation "'{{c' }}" := nil (at level 0) : ctx_scope.
  Notation "'{{c' bd , .. , bd' '}}'" :=
    (cons bd' .. (cons bd nil)..)
      (at level 0, bd custom ctx_binding at level 100,
          format "'[' {{c '[hv' bd ,  '/' .. ,  '/' bd' ']' }} ']'") : ctx_scope.

  Notation "bd , .. , bd'" :=
    (cons bd' .. (cons bd nil)..)
      (in custom ctx at level 100, bd custom ctx_binding at level 100,
          format "'[hv' bd ,  '/' .. ,  '/' bd' ']'") : ctx_scope.

  (* TODO: temporary holdover until { c } works*)
  Notation "! c" :=
    (c)
      (in custom ctx at level 0,
          c constr at level 0) : ctx_scope.

  Notation "" := nil (*(@nil (string*sort))*) (in custom ctx at level 0) : ctx_scope.

  Notation "x : t" :=
    (x%string, t)
      (in custom ctx_binding at level 100, x constr at level 0,
          t custom sort at level 100).

  Local Definition as_ctx (c:ctx) :=c.
  Check (as_ctx {{c }}).
  Check (as_ctx {{c "x" : #"env"}}).
  Check (as_ctx {{c "x" : #"env", "y" : #"ty" %"x", "z" : #"ty" %"x"}}).

End Notations.



Lemma with_names_from_args_subst (c':ctx) s' (s : list exp)
  : with_names_from c' s[/s'/] = (with_names_from c' s)[/s'/].
Proof using .
  elim: c' s; intros until s; case: s; intros; break; simpl in *; auto.
  f_equal; auto.
  by fold_Substable.
Qed.

(* TODO: move to utils! need more general types to do so; given in PfCore*)
Lemma map_fst_with_names_from (c:ctx) (s : list exp)
  : size s = size c -> map fst (with_names_from c s) = map fst c.
Proof using .
  elim: c s; intros until s; case: s; intros; break;simpl in *; auto.
  { inversion H0. }
  {
    f_equal; auto.
  }
Qed.

Lemma map_snd_with_names_from  (c:ctx) (s : list exp)
  : size s = size c -> map snd (with_names_from c s) = s.
Proof using .
  elim: c s; intros until s; case: s; intros; break;simpl in *; auto.
  { inversion H. }
  {
    f_equal; auto.
  }
Qed.
