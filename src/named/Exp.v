Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import List String.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.

Create HintDb exp discriminated.

Unset Elimination Schemes.
Inductive exp : Set :=
(* variable name *)
| var : string -> exp
(* Rule label, list of subterms*)
| con : string -> list exp -> exp.
Set Elimination Schemes.


(*Stronger induction principle w/ better subterm knowledge
 *)
Fixpoint exp_ind
         (P : exp -> Prop)
         (IHV : forall n, P(var n))
         (IHC : forall n l, all P l ->
             P (con n l))
         (e : exp) { struct e} : P e :=
  match e with
  | var n => IHV n
  | con n l =>
    let fix loop l :=
        match l return List.fold_right (fun t => and (P t)) True l with
        | [] => I
        | e' :: l' => conj (exp_ind _ IHV IHC e') (loop l')
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
        | [] => tt
        | e' :: l' => (exp_rect _ IHV IHC e', loop l')
        end in
    IHC n l (loop l)
  end.

Definition exp_rec := 
  exp_rect
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
  named_list_lookup (scon "" []) c n.

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

   Note: we could write this in bool using a decidable In (which is fine
   because strings have decidable equality)
 *)
Fixpoint ws_exp (args : list string) (e : exp) : Prop :=
  match e with
  | var x => In x args
  | con _ s => all (ws_exp args) s
  end.
Arguments ws_exp args !e/.

Definition ws_args args : list exp -> Prop := all (ws_exp args).
Arguments ws_args args !s/.

Fixpoint ws_subst args (s : subst) : Prop :=
  match s with
  | [] => True
  | (n,e)::s' => fresh n s' /\ ws_exp args e /\ ws_subst args s'
  end.
Arguments ws_subst args !s/.

Definition ws_sort args (t : sort) : Prop :=
  match t with scon _ s => ws_args args s end.
Arguments ws_sort args !t/.

Fixpoint ws_ctx (c : ctx) : Prop :=
  match c with
  | [] => True
  | (n,t) :: c' => fresh n c' /\ ws_sort (map fst c') t /\ ws_ctx c'
  end.
Arguments ws_ctx !c/.

Lemma ws_all_fresh_ctx c
  : ws_ctx c -> all_fresh c.
Proof using .
  induction c; basic_goal_prep; basic_utils_crush.
Qed.


Definition id_args {A} (c : named_list A) : list exp :=
  map var (map fst c).

Arguments id_args : simpl never.

(*Defined as a notation so that the definition 
does not get in the way of automation *)
Notation id_subst c := (with_names_from c (id_args c)).

Lemma id_args_cons A n (a :A) c
  : id_args ((n,a)::c) = (var n)::(id_args c).
Proof.
  reflexivity.
Qed.
Hint Rewrite id_args_cons : exp.

Class Substable (A : Type) : Type :=
  {
  apply_subst : subst -> A -> A;
  well_scoped : list string -> A -> Prop;
  subst_assoc : forall s1 s2 a,
      well_scoped (map fst s2) a ->
      apply_subst s1 (apply_subst s2 a) = apply_subst (subst_cmp s1 s2) a;
  subst_id : forall {A} (c : named_list A) a,
      (* Not necessary because of our choice of default
        well_scoped (map fst c) a ->*)
      apply_subst (id_subst c) a = a;
  strengthen_subst
  : forall s a n e,
      well_scoped (map fst s) a ->
      fresh n s ->
      apply_subst ((n,e)::s) a= apply_subst s a;
  well_scoped_subst args s a
    : ws_subst args s ->
      well_scoped (map fst s) a ->
      well_scoped args (apply_subst s a)
  }.

Arguments well_scoped {A}%type_scope {Substable} _%list_scope !_.
Arguments apply_subst {A}%type_scope {Substable} _%list_scope !_.
Hint Rewrite @subst_assoc : exp.
Hint Rewrite @subst_id : exp.
Hint Rewrite @strengthen_subst : exp.
#[export] Hint Resolve well_scoped_subst : exp.

Notation "e [/ s /]" := (apply_subst s e) (at level 7, left associativity).

Lemma exp_subst_nil e : exp_subst [] e = e.
Proof using .  
  induction e; basic_goal_prep; basic_utils_crush.
  f_equal.
  revert H.
  induction l; basic_goal_prep; basic_utils_crush.
Qed.
Hint Rewrite exp_subst_nil : exp.


Ltac basic_exp_crush := let x := autorewrite with utils exp in * in
                                  let y := eauto with utils exp in
                                          generic_crush x y.

Lemma named_map_subst_nil s : named_map (exp_subst []) s = s.
Proof using .
  induction s; basic_goal_prep;basic_exp_crush.
Qed.
Hint Rewrite named_map_subst_nil : exp.

Lemma subst_lookup_map s1 s2 n
  : In n (map fst s2) ->
          exp_subst s1 (subst_lookup s2 n) = subst_lookup (named_map (exp_subst s1) s2) n.
Proof using .
  induction s2; basic_goal_prep;
  basic_exp_crush.
  case_match; basic_exp_crush.
Qed.
Hint Rewrite subst_lookup_map : exp.
  
Lemma exp_subst_assoc : forall s1 s2 a,
    ws_exp (map fst s2) a ->
    exp_subst s1 (exp_subst s2 a)
    = exp_subst (subst_cmp s1 s2) a.
Proof using .
  induction a; basic_goal_prep;
    basic_exp_crush.
  f_equal.
  revert dependent l;
    induction l;
    basic_goal_prep;
    basic_exp_crush.
Qed.
Hint Rewrite exp_subst_assoc : exp.

Lemma subst_lookup_id A (c : named_list A) n
  : subst_lookup (id_subst c) n = var n.
Proof.
  induction c; basic_goal_prep;
    basic_exp_crush.
  (*TODO: get rid of need for symmetry*)
  case_match; symmetry in HeqH;
    basic_goal_prep;
    basic_exp_crush.
Qed.
Hint Rewrite subst_lookup_id : exp.

Lemma exp_subst_id
  : forall A (c : named_list A) a,
    exp_subst (id_subst c) a = a.
Proof.
  induction a; basic_goal_prep;
    basic_exp_crush.
  f_equal.
  revert dependent l;
    induction l;
    basic_goal_prep;
    basic_exp_crush.
Qed.
Hint Rewrite exp_subst_id : exp.

Lemma exp_strengthen_subst s a n e
  : ws_exp (map fst s) a ->
    fresh n s ->
    exp_subst ((n,e)::s) a = exp_subst s a.
Proof.
  induction a; basic_goal_prep; try case_match;
    basic_exp_crush.
  f_equal.

  revert dependent l.
  induction l; basic_goal_prep;
    basic_exp_crush.
Qed.

Lemma ws_exp_subst_lookup args s n
  : ws_subst args s ->
    In n (map fst s) ->
    ws_exp args (subst_lookup s n).
Proof.
  induction s; basic_goal_prep; try case_match;
    basic_exp_crush.
Qed.
#[export] Hint Resolve ws_exp_subst_lookup : exp.
  
Lemma exp_well_scoped_subst args s a
    : ws_subst args s ->
      ws_exp (map fst s) a ->
      ws_exp args (exp_subst s a).
Proof.
  induction a; basic_goal_prep; try case_match;
    basic_exp_crush.

  revert dependent l.
  induction l; basic_goal_prep;
    basic_exp_crush.
Qed.
Local Hint Resolve exp_well_scoped_subst : exp.
  
Instance substable_exp : Substable exp :=
  {
  apply_subst := exp_subst;
  well_scoped := ws_exp;
  subst_assoc := exp_subst_assoc;
  subst_id := exp_subst_id;
  strengthen_subst := exp_strengthen_subst;
  well_scoped_subst := exp_well_scoped_subst;
  }.
 
Lemma subst_subst_assoc : forall s1 s2 a,
    ws_subst (map fst s2) a ->
    subst_cmp s1 (subst_cmp s2 a)
    = subst_cmp (subst_cmp s1 s2) a.
Proof using .
  induction a; basic_goal_prep;
    basic_exp_crush.
Qed.

Lemma subst_subst_id
  : forall A (c : named_list A) a,
    subst_cmp (id_subst c) a = a.
Proof using .
  induction a; basic_goal_prep;
    basic_exp_crush.
Qed.

Lemma subst_strengthen_subst s a n e
  : ws_subst (map fst s) a ->
    fresh n s ->
    subst_cmp ((n,e)::s) a = subst_cmp s a.
Proof.
  induction a; basic_goal_prep; f_equal;
    basic_exp_crush.
  apply exp_strengthen_subst; auto.
Qed.

Lemma subst_well_scoped_subst args s a
    : ws_subst args s ->
      ws_subst (map fst s) a ->
      ws_subst args (subst_cmp s a).
Proof.
  induction a; basic_goal_prep; try case_match;
    basic_exp_crush.
Qed.
Local Hint Resolve subst_well_scoped_subst : exp.

Instance substable_subst : Substable subst :=
  {
  apply_subst := subst_cmp;
  well_scoped := ws_subst;
  subst_assoc := subst_subst_assoc;
  subst_id := subst_subst_id;
  strengthen_subst := subst_strengthen_subst;
  well_scoped_subst := subst_well_scoped_subst;
  }.

Definition args_subst s (a : list exp) := map (apply_subst s) a.
Arguments args_subst s !a/.

Lemma args_subst_assoc : forall s1 s2 a,
    ws_args (map fst s2) a ->
    args_subst s1 (args_subst s2 a)
    = args_subst (subst_cmp s1 s2) a.
Proof using .
  induction a; basic_goal_prep;
    basic_exp_crush.
Qed.

Lemma args_subst_id
  : forall A (c : named_list A) a,
    args_subst (id_subst c) a = a.
Proof using .
  induction a; basic_goal_prep;
    basic_exp_crush.
Qed.

Lemma args_strengthen_subst s a n e
  : ws_args (map fst s) a ->
    fresh n s ->
    args_subst ((n,e)::s) a = args_subst s a.
Proof.
  induction a; basic_goal_prep; f_equal;
    basic_exp_crush.
Qed.

Lemma args_well_scoped_subst args s a
    : ws_subst args s ->
      ws_args (map fst s) a ->
      ws_args args (args_subst s a).
Proof.
  induction a; basic_goal_prep; try case_match;
    basic_exp_crush.
Qed.
Local Hint Resolve args_well_scoped_subst : exp.

Instance substable_args : Substable (list exp) :=
  {
  apply_subst := args_subst;
  well_scoped := ws_args;
  subst_assoc := args_subst_assoc;
  subst_id := args_subst_id;
  strengthen_subst := args_strengthen_subst;
  well_scoped_subst := args_well_scoped_subst;
  }.

Definition sort_subst (s : subst) (t : sort) : sort :=
  let (c, s') := t in scon c s'[/s/].
Arguments sort_subst s !t/.

Lemma sort_subst_assoc : forall s1 s2 a,
    ws_sort (map fst s2) a ->
    sort_subst s1 (sort_subst s2 a)
    = sort_subst (subst_cmp s1 s2) a.
Proof using .
  destruct a; basic_goal_prep;
    basic_exp_crush.
Qed.


Lemma sort_subst_id
  : forall A (c : named_list A) a,
    sort_subst (id_subst c) a = a.
Proof using .
  destruct a; basic_goal_prep;
    basic_exp_crush.
Qed.


Lemma sort_strengthen_subst s a n e
  : ws_sort (map fst s) a ->
    fresh n s ->
    sort_subst ((n,e)::s) a = sort_subst s a.
Proof.
  destruct a; basic_goal_prep;
    basic_exp_crush.
Qed.

Lemma sort_well_scoped_subst args s a
    : ws_subst args s ->
      ws_sort (map fst s) a ->
      ws_sort args (sort_subst s a).
Proof.
  destruct a; basic_goal_prep; try case_match;
    basic_exp_crush.
Qed.

Instance substable_sort : Substable sort :=
  {
  subst_assoc := sort_subst_assoc;
  subst_id := sort_subst_id;
  strengthen_subst := sort_strengthen_subst;
  well_scoped_subst := sort_well_scoped_subst;
  }.


Fixpoint eq_exp e1 e2 {struct e1} : bool :=
  match e1, e2 with
  | var x, var y => eqb x y
  | con n1 l1, con n2 l2 =>
    (eqb n1 n2) && (all2 eq_exp l1 l2)
  | _,_ => false
  end.


Ltac fold_Substable :=
  try change (named_map (exp_subst ?s') ?s) with s[/s'/];
  try change (exp_subst ?s ?e) with e[/s/];
  try change (sort_subst ?s ?e) with e[/s/];
  try change (args_subst ?s ?e) with e[/s/];
  try change (subst_cmp ?s ?e) with e[/s/];
  try change (map (exp_var_map (subst_lookup ?s')) ?s) with s[/s'/].



(*Moved out of the module because Coq seems
  to include them at the the top level anyway
 *)
Declare Custom Entry exp.
Declare Custom Entry sort.


Declare Custom Entry ctx.
Declare Custom Entry ctx_binding.

Module Notations.

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
    (con c%string [])
      (right associativity,in custom exp at level 0, c constr at level 0,
                              format "# c").
  Notation "# c" :=
    (scon c%string [])
      (right associativity,in custom sort at level 0, c constr at level 0,
                              format "# c").

  Definition exp_constr_app e e' :=
    match e with
    | con c l => con c (e'::l)
    | _ => con "ERR" []
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
  revert s.
  induction c';
    destruct s;
    basic_goal_prep;
    basic_exp_crush.
Qed.

Lemma well_scoped_change_args A `{Substable A} (a:A) args args'
  : well_scoped args' a ->
    args = args' ->
    well_scoped args a.
Proof.  
  intros; subst; auto.
Qed.
#[export] Hint Resolve well_scoped_change_args : exp.


Ltac cbn_substs :=
  cbn [apply_subst with_names_from exp_subst subst_cmp args_subst sort_subst
                   substable_sort substable_args substable_exp substable_subst map
      exp_var_map subst_lookup named_list_lookup String.eqb Ascii.eqb Bool.eqb].
