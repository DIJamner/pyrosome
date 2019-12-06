Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From excomp Require Import Exp.

(* terms form a category over sorts w/ (empty or constant?) Γ *)
Inductive rule : Type :=
| sort :  ctx -> rule
| term :  ctx -> exp -> rule
| sort_le : ctx -> ctx -> exp -> exp -> rule
| term_le : ctx -> ctx -> exp -> exp -> exp -> exp -> rule.

Definition rule_map (f : exp -> exp) r : rule :=
  match r with
| sort c => sort (List.map f c)
| term c t => term (List.map f c) (f t)
| sort_le c1 c2 t1 t2 =>
  sort_le (List.map f c1) (List.map f c2) (f t1) (f t2)
| term_le  c1 c2 e1 e2 t1 t2 =>
  term_le (List.map f c1) (List.map f c2)
          (f e1) (f e2)
          (f t1) (f t2)
  end.

Bind Scope rule_scope with rule.
Delimit Scope rule_scope with rule.
Open Scope rule_scope.
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
Notation "{| c |- 'sort' }" := 
  (sort c) (at level 80) : rule_scope.
Notation "{| c |- s }" := 
  (term c s) (at level 80) : rule_scope.

Definition lang := list rule.

Definition ws_rule (r : rule) : bool :=
  match r with
  | {| c |- sort} => ws_ctx c
  | {| c |- t} => ws_ctx c && ws_exp (size c) t
  | {< c1 <# c2 |- s1 <# s2} =>
    ws_ctx c1
           && ws_exp (size c1) s1
           && ws_ctx c2
           && ws_exp (size c2) s2
  | {< c1 <# c2 |- e1 <# e2 .: s1 <# s2} =>
    ws_ctx c1
           && ws_exp (size c1) e1
           && ws_exp (size c1) s1
           && ws_ctx c2
           && ws_exp (size c2) e2
           && ws_exp (size c2) s2
  end.

Definition ws_lang : lang -> bool := List.forallb ws_rule.
