Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From excomp Require Import Utils Exp.

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

Definition eq_rule r1 r2 : bool :=
  match r1, r2 with
  | {| c1 |- sort }, {| c2 |- sort } => c1 == c2
  | {| c1 |- t1 }, {| c2 |- t2 } => (c1 == c2) && (t1 == t2)
  | {< c1 <# c2 |- t1 <# t2 },{< c1' <# c2' |- t1' <# t2' } =>
    (c1 == c1') && (t1 == t1') && (c2 == c2') && (t2 == t2')
  | {< c1 <# c2 |- e1 <# e2 .: t1 <# t2 },{< c1' <# c2' |- e1' <# e2' .: t1' <# t2' } =>
    (c1 == c1') && (e1 == e1') && (t1 == t1') && (c2 == c2')  && (e2 == e2') && (t2 == t2')
  | _,_ => false
  end.

Lemma eq_ruleP r1 r2 : reflect (r1 = r2) (eq_rule r1 r2).
Proof.
  case: r1 r2; intro_to rule; case; intros; simpl; eauto;
  try match goal with
  | |- reflect _ false => constructor; by inversion
  | |- reflect _ (?A == ?B) =>
    case eqcase: (A == B); constructor;
      solve [ by f_equal; apply /eqP
            | by case; move /eqP; rewrite eqcase]
      end.
  - match goal with
    | |- reflect _ (?E && _) => case and1: E; simpl
    end.
    match goal with
    | |- reflect _ false => constructor; by inversion
    | |- reflect _ (?A == ?B) =>
      case eqcase: (A == B); constructor;
        try solve [ by f_equal; apply /eqP
                  | by case; move /eqP; rewrite eqcase]
    end.
    case => _ => /eqP.
    by rewrite eqcase.
    constructor.
    case  => /eqP.
      by rewrite and1.
  - case ccs: (c == c1); simpl.
    case ecs: (e == e1); simpl.
    case c0cs: (c0 == c2); simpl.
    case e0cs: (e0 == e2); simpl.
    constructor; f_equal; by apply /eqP.
    constructor; case => _ _ _ /eqP; by rewrite e0cs.
    constructor; case => _ /eqP; by rewrite c0cs.
    constructor; case => _ _ /eqP; by rewrite ecs.
    constructor; case => /eqP; by rewrite ccs.
  - case ccs: (c == c1); simpl.
    case ecs: (e == e3); simpl.
    case e1cs: (e1 == e5); simpl.
    case c0cs: (c0 == c2); simpl.
    case e0cs: (e0 == e4); simpl.
    case e2cs: (e2 == e6); simpl.
    constructor; f_equal; by apply /eqP.
    constructor; case => _ _ _ _ _ /eqP; by rewrite e2cs.
    constructor; case => _ _ _ /eqP; by rewrite e0cs.
    constructor; case => _ /eqP; by rewrite c0cs.
    constructor; case => _ _ _ _ /eqP; by rewrite e1cs.
    constructor; case => _ _ /eqP; by rewrite ecs.
    constructor; case => /eqP; by rewrite ccs.
Qed.

Definition rule_eqMixin := Equality.Mixin eq_ruleP.

Canonical rule_eqType := @Equality.Pack rule rule_eqMixin.

Definition rule_constr_shift n r :=
  match r with
  | {| c |- sort } => {| map (constr_shift n) c |- sort}
  | {| c |- t } => {| map (constr_shift n) c |- constr_shift n t}
  | {< c1 <# c2 |- t1 <# t2 } =>
    {< map (constr_shift n) c1 <# map (constr_shift n) c2
     |- constr_shift n t1 <# constr_shift n t2 }
  | {< c1 <# c2 |- e1 <# e2 .: t1 <# t2 } =>
    {< map (constr_shift n) c1 <# map (constr_shift n) c2
     |- constr_shift n e1 <# constr_shift n e2
                     .: constr_shift n t1 <# constr_shift n t2}
  end.

Notation "r %%! n" := (rule_constr_shift n r) (at level 7).


Lemma rule_constr_shift_shift r n m : r%%!n %%!m = r%%!(n+m).
Proof.
  case: r; simpl; intros; f_equal;
    move: constr_shift_shift map_constr_shift_shift;
  auto.
Qed.

Definition rule_constr_downshift n r : option rule :=
  match r with
  | {| c |- sort } => c' <- try_map (constr_downshift n) c; Some ({| c' |- sort})
  | {| c |- t } =>
    c' <- try_map (constr_downshift n) c;
      t' <- constr_downshift n t;
      Some ({| c' |- t'})
  | {< c1 <# c2 |- t1 <# t2 } =>
    c1' <- try_map (constr_downshift n) c1;
      c2' <- try_map (constr_downshift n) c2;
      t1' <- constr_downshift n t1;
      t2' <- constr_downshift n t2;
      Some ({< c1' <# c2' |- t1' <# t2' })
  | {< c1 <# c2 |- e1 <# e2 .: t1 <# t2 } =>
    c1' <- try_map (constr_downshift n) c1;
      c2' <- try_map (constr_downshift n) c2;
      e1' <- constr_downshift n e1;
      e2' <- constr_downshift n e2;
      t1' <- constr_downshift n t1;
      t2' <- constr_downshift n t2;
      Some ({< c1' <# c2' |- e1' <# e2' .: t1' <# t2'})
  end.

Lemma rule_downshift_left_inverse r n : rule_constr_downshift n r%%!n = Some r.
Proof.
  case: r => //=;
  intros;
  rewrite ?downshift_left_inverse ?try_map_downshift_left_inverse;
  by compute.
Qed.
