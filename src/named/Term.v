Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import List String.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
Import SumboolNotations.

Create HintDb term discriminated.

Unset Elimination Schemes.
Inductive term : Set :=
(* variable name *)
| var : string -> term
(* Rule label, list of subterms*)
| con : string -> list term -> term.
Set Elimination Schemes.

Coercion var : string >-> term.

(*Stronger induction principle w/ better subterm knowledge
 *)
Fixpoint term_ind
         (P : term -> Prop)
         (IHV : forall n, P(var n))
         (IHC : forall n l, all P l ->
             P (con n l))
         (e : term) { struct e} : P e :=
  match e with
  | var n => IHV n
  | con n l =>
    let fix loop l :=
        match l return List.fold_right (fun t => and (P t)) True l with
        | [] => I
        | e' :: l' => conj (term_ind _ IHV IHC e') (loop l')
        end in
    IHC n l (loop l)
  end.

Fixpoint term_rect
         (P : term -> Type)
         (IHV : forall n, P(var n))
         (IHC : forall n l,
             List.fold_right (fun t => prod (P t)) unit l ->
             P (con n l))
         (e : term) { struct e} : P e :=
  match e with
  | var n => IHV n
  | con n l =>
    let fix loop l :=
        match l return List.fold_right (fun t => prod (P t)) unit l with
        | [] => tt
        | e' :: l' => (term_rect _ IHV IHC e', loop l')
        end in
    IHC n l (loop l)
  end.

Definition term_rec := 
  term_rect
     : forall P : term -> Set,
       (forall n, P (var n)) ->
       (forall n l,
             List.fold_right (fun t => prod (P t)) unit l ->
             P (con n l))-> forall e : term, P e.

Variant sort : Set := scon : string -> list term -> sort.

Lemma invert_eq_var_var x y
  : var x = var y <-> x = y.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_var_var : term.

Lemma invert_eq_var_con x n s
  : var x = con n s <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_var_con : term.

Lemma invert_eq_con_var n s y
  : con n s = var y <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_con_var : term.

Definition ctx : Set := named_list_set sort.

Definition subst : Set := named_list_set term.

Definition subst_lookup (s : subst) (n : string) : term :=
  named_list_lookup (var n) s n.

Arguments subst_lookup !s n/.

Definition ctx_lookup (c: ctx) (n : string) : sort :=
  named_list_lookup (scon "" []) c n.

Arguments ctx_lookup !c n/.


Fixpoint term_var_map (f : string -> term) (e : term) : term :=
  match e with
  | var n => f n
  | con n l => con n (map (term_var_map f) l)
  end.

Arguments term_var_map f !e /.

Definition term_subst (s : subst) e : term :=
  term_var_map (subst_lookup s) e.

Arguments term_subst s !e /.

Definition subst_cmp s1 s2 : subst := named_map (term_subst s1) s2.
Arguments subst_cmp s1 s2 /.

(* Well-scoped languages
   Written as functions that decide the properties
   determines that variables (but not constructor symbols) are well-scoped

   Note: we could write this in bool using a decidable In (which is fine
   because strings have decidable equality)
 *)
Fixpoint ws_term (args : list string) (e : term) : Prop :=
  match e with
  | var x => In x args
  | con _ s => all (ws_term args) s
  end.
Arguments ws_term args !e/.

Definition ws_args args : list term -> Prop := all (ws_term args).
Arguments ws_args args !s/.

Fixpoint ws_subst args (s : subst) : Prop :=
  match s with
  | [] => True
  | (n,e)::s' => fresh n s' /\ ws_term args e /\ ws_subst args s'
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


Definition id_args {A} (c : named_list A) : list term :=
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
Hint Rewrite id_args_cons : term.

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
Hint Rewrite @subst_assoc : term.
Hint Rewrite @subst_id : term.
Hint Rewrite @strengthen_subst : term.
#[export] Hint Resolve well_scoped_subst : term.

Notation "e [/ s /]" := (apply_subst s e) (at level 7, left associativity).

Lemma term_subst_nil e : term_subst [] e = e.
Proof using .  
  induction e; basic_goal_prep; basic_utils_crush.
  f_equal.
  revert H.
  induction l; basic_goal_prep; basic_utils_crush.
Qed.
Hint Rewrite term_subst_nil : term.


Ltac basic_term_crush := let x := autorewrite with utils term in * in
                                  let y := eauto with utils term in
                                          generic_crush x y.

Lemma named_map_subst_nil s : named_map (term_subst []) s = s.
Proof using .
  induction s; basic_goal_prep;basic_term_crush.
Qed.
Hint Rewrite named_map_subst_nil : term.

Lemma subst_lookup_map s1 s2 n
  : In n (map fst s2) ->
          term_subst s1 (subst_lookup s2 n) = subst_lookup (named_map (term_subst s1) s2) n.
Proof using .
  induction s2; basic_goal_prep;
  basic_term_crush.
  case_match; basic_term_crush.
Qed.
Hint Rewrite subst_lookup_map : term.
  
Lemma term_subst_assoc : forall s1 s2 a,
    ws_term (map fst s2) a ->
    term_subst s1 (term_subst s2 a)
    = term_subst (subst_cmp s1 s2) a.
Proof using .
  induction a; basic_goal_prep;
    basic_term_crush.
  f_equal.
  revert dependent l;
    induction l;
    basic_goal_prep;
    basic_term_crush.
Qed.
Hint Rewrite term_subst_assoc : term.

Lemma subst_lookup_id A (c : named_list A) n
  : subst_lookup (id_subst c) n = var n.
Proof.
  induction c; basic_goal_prep;
    basic_term_crush.
  (*TODO: get rid of need for symmetry*)
  case_match; symmetry in HeqH;
    basic_goal_prep;
    basic_term_crush.
Qed.
Hint Rewrite subst_lookup_id : term.

Lemma term_subst_id
  : forall A (c : named_list A) a,
    term_subst (id_subst c) a = a.
Proof.
  induction a; basic_goal_prep;
    basic_term_crush.
  f_equal.
  revert dependent l;
    induction l;
    basic_goal_prep;
    basic_term_crush.
Qed.
Hint Rewrite term_subst_id : term.

Lemma term_strengthen_subst s a n e
  : ws_term (map fst s) a ->
    fresh n s ->
    term_subst ((n,e)::s) a = term_subst s a.
Proof.
  induction a; basic_goal_prep; try case_match;
    basic_term_crush.
  f_equal.

  revert dependent l.
  induction l; basic_goal_prep;
    basic_term_crush.
Qed.

Lemma ws_term_subst_lookup args s n
  : ws_subst args s ->
    In n (map fst s) ->
    ws_term args (subst_lookup s n).
Proof.
  induction s; basic_goal_prep; try case_match;
    basic_term_crush.
Qed.
#[export] Hint Resolve ws_term_subst_lookup : term.
  
Lemma term_well_scoped_subst args s a
    : ws_subst args s ->
      ws_term (map fst s) a ->
      ws_term args (term_subst s a).
Proof.
  induction a; basic_goal_prep; try case_match;
    basic_term_crush.

  revert dependent l.
  induction l; basic_goal_prep;
    basic_term_crush.
Qed.
Local Hint Resolve term_well_scoped_subst : term.
  
Instance substable_term : Substable term :=
  {
  apply_subst := term_subst;
  well_scoped := ws_term;
  subst_assoc := term_subst_assoc;
  subst_id := term_subst_id;
  strengthen_subst := term_strengthen_subst;
  well_scoped_subst := term_well_scoped_subst;
  }.
 
Lemma subst_subst_assoc : forall s1 s2 a,
    ws_subst (map fst s2) a ->
    subst_cmp s1 (subst_cmp s2 a)
    = subst_cmp (subst_cmp s1 s2) a.
Proof using .
  induction a; basic_goal_prep;
    basic_term_crush.
Qed.

Lemma subst_subst_id
  : forall A (c : named_list A) a,
    subst_cmp (id_subst c) a = a.
Proof using .
  induction a; basic_goal_prep;
    basic_term_crush.
Qed.

Lemma subst_strengthen_subst s a n e
  : ws_subst (map fst s) a ->
    fresh n s ->
    subst_cmp ((n,e)::s) a = subst_cmp s a.
Proof.
  induction a; basic_goal_prep; f_equal;
    basic_term_crush.
  apply term_strengthen_subst; auto.
Qed.

Lemma subst_well_scoped_subst args s a
    : ws_subst args s ->
      ws_subst (map fst s) a ->
      ws_subst args (subst_cmp s a).
Proof.
  induction a; basic_goal_prep; try case_match;
    basic_term_crush.
Qed.
Local Hint Resolve subst_well_scoped_subst : term.

Instance substable_subst : Substable subst :=
  {
  apply_subst := subst_cmp;
  well_scoped := ws_subst;
  subst_assoc := subst_subst_assoc;
  subst_id := subst_subst_id;
  strengthen_subst := subst_strengthen_subst;
  well_scoped_subst := subst_well_scoped_subst;
  }.

Definition args_subst s (a : list term) := map (apply_subst s) a.
Arguments args_subst s !a/.

Lemma args_subst_assoc : forall s1 s2 a,
    ws_args (map fst s2) a ->
    args_subst s1 (args_subst s2 a)
    = args_subst (subst_cmp s1 s2) a.
Proof using .
  induction a; basic_goal_prep;
    basic_term_crush.
Qed.

Lemma args_subst_id
  : forall A (c : named_list A) a,
    args_subst (id_subst c) a = a.
Proof using .
  induction a; basic_goal_prep;
    basic_term_crush.
Qed.

Lemma args_strengthen_subst s a n e
  : ws_args (map fst s) a ->
    fresh n s ->
    args_subst ((n,e)::s) a = args_subst s a.
Proof.
  induction a; basic_goal_prep; f_equal;
    basic_term_crush.
Qed.

Lemma args_well_scoped_subst args s a
    : ws_subst args s ->
      ws_args (map fst s) a ->
      ws_args args (args_subst s a).
Proof.
  induction a; basic_goal_prep; try case_match;
    basic_term_crush.
Qed.
Local Hint Resolve args_well_scoped_subst : term.

Instance substable_args : Substable (list term) :=
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
    basic_term_crush.
Qed.


Lemma sort_subst_id
  : forall A (c : named_list A) a,
    sort_subst (id_subst c) a = a.
Proof using .
  destruct a; basic_goal_prep;
    basic_term_crush.
Qed.


Lemma sort_strengthen_subst s a n e
  : ws_sort (map fst s) a ->
    fresh n s ->
    sort_subst ((n,e)::s) a = sort_subst s a.
Proof.
  destruct a; basic_goal_prep;
    basic_term_crush.
Qed.

Lemma sort_well_scoped_subst args s a
    : ws_subst args s ->
      ws_sort (map fst s) a ->
      ws_sort args (sort_subst s a).
Proof.
  destruct a; basic_goal_prep; try case_match;
    basic_term_crush.
Qed.

Instance substable_sort : Substable sort :=
  {
  subst_assoc := sort_subst_assoc;
  subst_id := sort_subst_id;
  strengthen_subst := sort_strengthen_subst;
  well_scoped_subst := sort_well_scoped_subst;
  }.


Fixpoint eq_term e1 e2 {struct e1} : bool :=
  match e1, e2 with
  | var x, var y => eqb x y
  | con n1 l1, con n2 l2 =>
    (eqb n1 n2) && (all2 eq_term l1 l2)
  | _,_ => false
  end.


Ltac fold_Substable :=
  try change (named_map (term_subst ?s') ?s) with s[/s'/];
  try change (term_subst ?s ?e) with e[/s/];
  try change (sort_subst ?s ?e) with e[/s/];
  try change (args_subst ?s ?e) with e[/s/];
  try change (subst_cmp ?s ?e) with e[/s/];
  try change (map (term_var_map (subst_lookup ?s')) ?s) with s[/s'/].



(*Moved out of the module because Coq seems
  to include them at the the top level anyway
 *)
Declare Custom Entry term.
Declare Custom Entry sort.

Declare Custom Entry arg_list.
Declare Custom Entry arg.


Declare Custom Entry ctx.
Declare Custom Entry ctx_binding.

Module Notations.

  (* Since contexts are regular lists, 
     we need a scope to determine when to print them *)
  Declare Scope ctx_scope.
  Bind Scope ctx_scope with ctx.
  
  Notation "'{{e' e }}" :=
    (e) (at level 0,
         e custom term at level 100,
         format "'[' '{{e'  e '}}' ']'").
  Notation "'{{s' e }}" :=
    (e) (at level 0,
         e custom sort at level 100,
         format "'[' '{{s'  e '}}' ']'").
  
  Notation "{ x }" :=
    x (in custom term at level 0, x constr).
  Notation "{ x }" :=
    x (in custom arg at level 0, x constr).
  Notation "{ x }" :=
    x (in custom sort at level 0, x constr).
  (* TODO: issues; fix *)
  (*
    Notation "{ x }" :=
    x (in custom ctx at level 0, x constr).
  *)
  
  Notation "# c" :=
    (con c%string [])
      (right associativity,in custom arg at level 0, c constr at level 0,
                              format "# c").
  Notation "( e )" := e (in custom arg at level 0, e custom term at level 100).

  Notation "" := [] (in custom arg_list at level 0).
  Notation "a1 .. an" :=
    (cons an .. (cons a1 nil) ..)
      (right associativity,
        in custom arg_list at level 50,
           a1 custom arg, an custom arg,
           format " '[hv' a1  ..  an ']'"
      ).
  
  Notation "# c al" :=
    (con c%string al)
      (right associativity,
        in custom term at level 60,
           c constr at level 0,
           al custom arg_list,
           format "'[' # c al ']'").
  
  Notation "# c al" :=
    (scon c%string al)
      (right associativity,
        in custom sort at level 60,
           c constr at level 0,
           al custom arg_list,
           format "'[' # c al ']'").
  
  Notation "x" :=
    (var x%string)
      (in custom term at level 0, x constr at level 0, format "x").
  
  Notation "x" :=
    (var x%string)
      (in custom arg at level 0, x constr at level 0, format "x").

  
  (* TODO: allow redundant parens?
  Notation "( e )" := e (in custom term at level 0, e custom term at level 100).
  Notation "( e )" := e (in custom sort at level 0, e custom sort at level 100).
   *)


  Check {{e #"foo" }}.
  Check {{e #"foo" (#"bar" "x") #"baz" "y"}}.
  Check {{s #"foo" }}.
  Check {{s #"foo" (#"bar" "x") #"baz" "y"}}.
  Check (fun n s => con n [s]).
                               
  Bind Scope ctx_scope with ctx.

  Notation "'{{c' }}" :=
    nil
      (at level 0, format "'[' '{{c'  '}}' ']'")
    : ctx_scope.
  Notation "'{{c' bd , .. , bd' '}}'" :=
    (cons bd' .. (cons bd nil)..)
      (at level 0, bd custom ctx_binding at level 100,
          format "'[' {{c  '[hv' bd ,  '/' .. ,  '/' bd' ']' }} ']'") : ctx_scope.

  Notation "bd , .. , bd'" :=
    (cons bd' .. (cons bd nil)..)
      (in custom ctx at level 100, bd custom ctx_binding at level 100,
          format "'[hv' bd ,  '/' .. ,  '/' bd' ']'") : ctx_scope.

  (*
  (* TODO: find uses and update*)
  Notation "! c" :=
    (c)
      (in custom ctx at level 0,
          c constr at level 0) : ctx_scope.
   *)

  Notation "" := nil (*(@nil (string*sort))*) (in custom ctx at level 0) : ctx_scope.

  Notation "x : t" :=
    (x%string, t)
      (in custom ctx_binding at level 100, x constr at level 0,
          t custom sort at level 100).

  Local Definition as_ctx (c:ctx) :=c.
  Check (as_ctx {{c }}).
  Check (as_ctx {{c "x" : #"env"}}).
  Check (as_ctx {{c "x" : #"env", "y" : #"ty" "x", "z" : #"ty" "x"}}).

End Notations.



Lemma with_names_from_args_subst (c':ctx) s' (s : list term)
  : with_names_from c' s[/s'/] = (with_names_from c' s)[/s'/].
Proof using .
  revert s.
  induction c';
    destruct s;
    basic_goal_prep;
    basic_term_crush.
Qed.

Lemma well_scoped_change_args A `{Substable A} (a:A) args args'
  : well_scoped args' a ->
    args = args' ->
    well_scoped args a.
Proof.  
  intros; subst; auto.
Qed.
#[export] Hint Resolve well_scoped_change_args : term.


Ltac cbn_substs :=
  cbn [apply_subst with_names_from term_subst subst_cmp args_subst sort_subst
                   substable_sort substable_args substable_term substable_subst map
      term_var_map subst_lookup named_list_lookup String.eqb Ascii.eqb Bool.eqb].



Lemma invert_con n n' s s'
  : con n s = con n' s' <-> n = n' /\ s = s'.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_con : term.

Lemma invert_var_con n s x
  : var x = con n s <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_var_con : term.

Lemma invert_con_var n s x
  : con n s = var x <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_var_con : term.


Lemma invert_scon n n' s s'
  : scon n s = scon n' s' <-> n = n' /\ s = s'.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_scon : term.

(*TODO: put in substable?*)
(*TODO: guarentee all_fresh or no?*)
Fixpoint fv e : list string :=
  match e with
  | var x => [x]
  | con _ s => flat_map fv s
  end.

Definition fv_args := flat_map fv.

Definition fv_sort (t:sort) :=
  let (_,s) := t in
  fv_args s.


Fixpoint term_eq_dec (e1 e2 : term) {struct e1} : {e1 = e2} + {~ e1 = e2}.
  refine(match e1, e2 with
         | var x, var y => SB! string_dec x y
         | con n s, con n' s' =>
           SB! (string_dec n n') SB& (list_eq_dec term_eq_dec s s')
         | _, _ => right _
         end); basic_term_crush.
Defined.


Definition sort_eq_dec (e1 e2 : sort) : {e1 = e2} + {~ e1 = e2}.
  refine(match e1, e2 with
         | scon n s, scon n' s' =>
           SB! (string_dec n n') SB& (list_eq_dec term_eq_dec s s')
         end); basic_term_crush.
Defined.

Definition ctx_eq_dec := list_eq_dec (pair_eq_dec string_dec sort_eq_dec).