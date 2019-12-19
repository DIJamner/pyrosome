Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From excomp Require Import Exp Rule CoreDefs Core.

Require Import String.

Inductive nexp : Set :=
| nvar : nat -> nexp
(* Rule deBruijn index, list of subterms*)
| ncon : string -> seq nexp -> nexp.

Definition nctx := seq nexp.

(* terms form a category over sorts w/ (empty or constant?) Γ *)
Inductive named_rule : Type :=
| nsort : nctx -> string->  named_rule
| nterm : nctx -> string -> nexp -> named_rule
| nsort_le : nctx -> nctx -> nexp -> nexp -> named_rule
| nterm_le : nctx -> nctx -> nexp -> nexp -> nexp -> nexp -> named_rule.

Bind Scope nrule_scope with named_rule.
Delimit Scope nrule_scope with named_rule.
Open Scope nrule_scope.
Notation "{<n c1 <# c2 |- s1 <# s2 }" := (nsort_le c1 c2 s1 s2) (at level 80) : rule_scope.
Notation "{<n c |- s1 <# s2 }" := (sort_le c c s1 s2) (at level 80):rule_scope.
Notation "{<n c |- s }" := (sort_le c c s s) (at level 80):rule_scope.
Notation "{<n c1 <# c2 |- e1 <# e2 .: s1 <# s2 }" :=
  (nterm_le c1 c2 e1 e2 s1 s2) (at level 80) : rule_scope.
Notation "{<n c |- e1 <# e2 .: s1 <# s2 }" :=
  (nterm_le c c e1 e2 s1 s2) (at level 80) : rule_scope.
Notation "{<n c |- e1 <# e2 .: s }" :=
  ({<n c |- e1 <# e2 .: s <# s}) (at level 80) : rule_scope.
Notation "{<n c |- e .: s }" := 
  ({< c |- e <# e.: s}) (at level 80) : rule_scope.
Notation "{|n c |- name 'sort' }" := 
  (nsort c name) (at level 80) : rule_scope.
Notation "{|n c |- name .: s }" := 
  (nterm c name s) (at level 80) : rule_scope.

Fixpoint idx (l : seq string) (a : string) : nat :=
  match l with
  | [::] => 0
  | a'::l' => if eqb a a' then 0 else (idx l' a).+1
  end.

Fixpoint index_named_exp nl (e : nexp) : exp :=
  match e with
  | nvar n => var n
  | ncon s l => con (idx nl s) (map (index_named_exp nl) l)
  end.

Definition index_named_rule nl (r : named_rule) : rule :=
  match r with
  | {|n c |- nm sort } => {| map (index_named_exp nl) c |- sort }
  | {|n c |- nm .: s } => {| map (index_named_exp nl) c |- index_named_exp nl s }
  | {<n c1 <# c2 |- s1 <# s2 } =>
    {< map (index_named_exp nl) c1
           <# map (index_named_exp nl) c2
     |- index_named_exp nl s1 <# index_named_exp nl s2}
  | {<n c1 <# c2 |- e1 <# e2 .: s1 <# s2 } =>
    {< map (index_named_exp nl) c1
           <# map (index_named_exp nl) c2
     |- index_named_exp nl e1 <# index_named_exp nl e2
    .: index_named_exp nl s1 <# index_named_exp nl s2}
  end.

Definition name_of (r : named_rule) : string :=
  match r with
  | {|n c |- nm sort } => nm
  | {|n c |- nm .: s } => nm
  | {<n c1 <# c2 |- s1 <# s2 } => "@#!$"
  | {<n c1 <# c2 |- e1 <# e2 .: s1 <# s2 } => "@#!$"
  end.

Fixpoint index_nlang' (nl : seq string) (l : seq named_rule) : lang * seq string :=
  match l with
  | [::] => ([::],[::])
  | r :: l' =>
    let (lout,nl') := index_nlang' nl l' in
    let rout := index_named_rule nl' r in
    let rn := name_of r in
    (rout::lout, rn::nl')
  end.

Definition index_nlang l :=
  let (lout,_):= index_nlang' [::] l in
  lout.
