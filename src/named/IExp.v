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
with sort : Set := srt : string -> list exp -> sort.
Set Elimination Schemes.


Definition ctx : Set := named_list_set sort.

Definition subst : Set := named_list_set exp.

Definition subst_lookup (s : subst) (n : string) : exp :=
  named_list_lookup (var n) s n.
Global Transparent subst_lookup.

Definition ctx_lookup (c: ctx) (n : string) : sort :=
  named_list_lookup (srt "" [::]) c n.
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
       | srt n s => srt n (map (exp_var_map f) s)
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
  let (c, s') := t in srt c (map (apply_subst s) s').

Lemma sort_subst_assoc : forall s1 s2 a,
    sort_subst s1 (sort_subst s2 a)
    = sort_subst (subst_cmp s1 s2) a.
Admitted.

Instance substable_sort : Substable sort :=
  {
  apply_subst := sort_subst;
  subst_assoc := sort_subst_assoc;
  }.
