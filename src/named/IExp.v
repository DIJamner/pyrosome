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
| con : string -> list exp -> exp
| ann : exp -> sort -> exp                         
with sort : Set := scon : string -> list exp -> sort.
Set Elimination Schemes.


Definition ctx : Set := named_list_set sort.

Definition subst : Set := named_list_set exp.

Definition subst_lookup (s : subst) (n : string) : exp :=
  named_list_lookup (var n) s n.
Global Transparent subst_lookup.

Definition ctx_lookup (c: ctx) (n : string) : sort :=
  named_list_lookup (scon "ERR" [::]) c n.
Global Transparent ctx_lookup.

(*TODO: move to utils*)
Definition pair_map_snd {A B C} (f : B -> C) (p : A * B) :=
  let (a,b) := p in (a, f b).

Definition named_map {A B : Set} (f : A -> B) : named_list A -> named_list B
  := map (pair_map_snd f).

Fixpoint exp_var_map (f : string -> exp) (e : exp) : exp :=
  match e with
  | var n => f n
  | con n l => con n (map (exp_var_map f) l)
  | ann e t => ann (exp_var_map f e) (sort_var_map f t)
  end
with sort_var_map f t :=
       match t with
       | scon n s => scon n (map (exp_var_map f) s)
       end.

Definition exp_subst (s : subst) e : exp :=
  exp_var_map (subst_lookup s) e.

Definition subst_cmp s1 s2 : subst := named_map (exp_subst s2) s1.

Class Substable (A : Set) : Set :=
  {
  apply_subst : subst -> A -> A;
  subst_assoc : forall s1 s2 a,
      apply_subst s1 (apply_subst s2 a) = apply_subst (subst_cmp s1 s2) a
(* TODO: identity law*)
  }.

Notation "e [/ s /]" := (apply_subst s e) (at level 7, left associativity).

Lemma exp_subst_assoc : forall s1 s2 a,
    exp_subst s1 (exp_subst s2 a)
    = exp_subst (subst_cmp s1 s2) a.
Admitted.

Instance substable_exp : Substable exp :=
  {
  apply_subst := exp_subst;
  subst_assoc := exp_subst_assoc;
  }.
 
Lemma subst_subst_assoc : forall s1 s2 a,
    subst_cmp s1 (subst_cmp a s2)
    = subst_cmp (subst_cmp s1 s2) a.
Admitted.

#[refine]
Instance substable_subst : Substable subst :=
  {
  apply_subst := (fun s1 s2 => subst_cmp s2 s1)
  }.
intros.
by rewrite subst_subst_assoc.
Defined.

Definition sort_subst (s : subst) (t : sort) : sort :=
  let (c, s') := t in scon c (map (apply_subst s) s').

Lemma sort_subst_assoc : forall s1 s2 a,
    sort_subst s1 (sort_subst s2 a)
    = sort_subst (subst_cmp s1 s2) a.
Admitted.

Instance substable_sort : Substable sort :=
  {
  apply_subst := sort_subst;
  subst_assoc := sort_subst_assoc;
  }.

Module Notations.

  Declare Custom Entry exp.
  Declare Custom Entry sort.
  

  Declare Custom Entry ctx.
  Declare Custom Entry ctx_binding.

  (* Since contexts are regular lists, 
     we need a scope to determine when to print them *)
  Declare Scope ctx_scope.
  Bind Scope ctx_scope with ctx.

  (* for notation purposes *)
  Definition as_ctx (c : ctx) := c.
  
  Notation "'{{e' e }}" := (e) (at level 0,e custom exp at level 100).
  Notation "'{{s' e }}" := (e) (at level 0,e custom sort at level 100).
  Notation "'{{c' e }}" := (as_ctx e) (at level 0,e custom ctx at level 100).
  
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

  Check {{c }}.
  Check {{c "x" : #"env"}}.
  Check {{c "x" : #"env", "y" : #"ty" %"x", "z" : #"ty" %"x"}}.

  Check let c := {{c }} in {{c !c}}.

End Notations.
