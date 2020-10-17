Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From Utils Require Import Utils.
From Named Require Import Exp.

(* terms form a category over sorts w/ (empty or constant?) Γ *)
Inductive rule : Type :=
| sort_rule :  ctx -> rule
| term_rule :  ctx -> sort -> rule
| sort_le : ctx -> sort -> sort -> rule
| term_le : ctx -> exp -> exp -> sort -> rule.


Bind Scope rule_scope with rule.
Delimit Scope rule_scope with rule.

Declare Custom Entry expr.
Declare Custom Entry srt.
Declare Custom Entry subst.
Declare Custom Entry ctx.

Require Import String.

Declare Custom Entry subst_binding.

Notation "# c ( e , .. , e' )" :=
  (con c%string (cons e' .. (cons e nil) ..))
    (in custom expr at level 0, c constr at level 0,
    e custom expr, e' custom expr).

Notation "e / x" :=
  (x%string,e) (in custom subst_binding at level 0,
        e custom expr, x constr at level 0).

Notation "# c" :=
  (con c%string [::])
    (in custom expr at level 0, c constr at level 0).

Notation "# c ( e , .. , e' )" :=
  (srt c%string (cons e' .. (cons e nil) ..))
    (in custom srt at level 0, c constr at level 0,
    e custom expr, e' custom expr).

Notation "! x" :=
  x (in custom expr at level 0, x ident).
Notation "! x" :=
  x (in custom srt at level 0, x ident).
Notation "! x" :=
  x (in custom subst at level 0, x ident).
Notation "! x" :=
  x (in custom ctx at level 0, x ident).

               
Notation "% x" :=
  (var x%string)
    (in custom expr at level 0, x constr at level 0).

Notation "# c" :=
  (srt c%string [::])
    (in custom srt at level 0, c constr at level 0).

Notation "'[s|' G |- s ]" :=
  (s%string, sort_rule G)
    (s constr at level 0, G custom ctx
(*    format "'[  ' G '/' '|-s' s ']'").*)).

Notation "[:| G |- s : t ]" :=
  (s%string, term_rule G t)
    (t custom srt,
     s constr at level 0, G custom ctx
    (*format "'[  ' G '/' |- '[  ' s '/' : t ']' ']'"*)).

Notation "'[s>' G |- ( s ) e1 = e2 ]" :=
  (s%string, sort_le G e1 e2)
    (s constr at level 0, G custom ctx,
     e1 custom srt, e2 custom srt).

Notation "[:> G |- ( s ) e1 = e2 : t ]" :=
  (s%string, term_le G e1 e2 t)
    (s constr at level 0, G custom ctx,
     t custom srt, e1 custom expr, e2 custom expr).

Notation "'[s|' |- s ]" :=
  (s%string, sort_rule [::])
    (s constr at level 0).

Notation "[:| |- s : t ]" :=
  (s%string, term_rule [::] t)
    (t custom srt,
     s constr at level 0
    (*format "'[  ' G '/' |- '[  ' s '/' : t ']' ']'"*)).

Notation "'[s>' |- ( s ) e1 = e2 ]" :=
  (s%string, sort_le [::] e1 e2)
    (s constr at level 0,
     e1 custom srt, e2 custom srt).

Notation "[:> |- ( s ) e1 = e2 : t ]" :=
  (s%string, term_le [::] e1 e2 t)
    (s constr at level 0,
     t custom srt, e1 custom expr, e2 custom expr).

(*Notation "(:)" := [::] (in custom ctx).*)

(*

Notation "'|-s' s" :=
  (s%string, sort_rule [::])
    (in custom rule at level 80, s constr at level 0).

Notation "|- s : t" :=
  (s%string, term_rule [::] t)
    (in custom rule at level 81, t custom srt,
     s constr at level 0,
    format "'[  ' |- '[  ' s '/' : t ']' ']'").

Notation "'|-s' ( s ) e1 = e2" :=
  (s%string, sort_le [::] e1 e2)
    (in custom rule at level 82,
     s constr at level 0,
     e1 custom srt, e2 custom srt).

Notation "|- ( s ) e1 = e2 : t" :=
  (s%string, term_le [::] e1 e2 t)
    (in custom rule at level 83,
     s constr at level 0,
     t custom srt, e1 custom expr, e2 custom expr).
*)

Declare Custom Entry ctx_binding.

Notation "bd , .. , bd'" :=
  (cons bd' .. (cons bd nil)..)
    (in custom ctx at level 100, bd custom ctx_binding).

Notation "x : t" :=
  (x%string, t)
    (in custom ctx_binding at level 100, x constr at level 0,
        t custom srt).

Print Grammar constr.
Check [:| "x" : #"foo", "y" : #"bar" |- "foo" : #"bar" (#"baz", #"qux")].
Check [s> |- ("eq")#"foo" = #"bar"].
(*TODO: get printing working! are list notations interfering?*)

Definition lang := named_list rule.

(*
Definition ws_rule (r : rule) : bool :=
  match r with
  | {| c |- sort} => ws_ctx c
  | {| c |- t} => ws_ctx c && ws_exp (size c) t
  | {< c |- s1 <# s2} =>
    ws_ctx c
           && ws_exp (size c) s1
           && ws_exp (size c) s2
  | {< c |- e1 <# e2 .: s} =>
    ws_ctx c
           && ws_exp (size c) e1
           && ws_exp (size c) e2
           && ws_exp (size c) s
  end.

Definition ws_lang : lang -> bool := List.forallb ws_rule.
*)

Definition eq_rule r1 r2 : bool :=
  match r1, r2 with
  | sort_rule c1, sort_rule c2 => c1 == c2
  | term_rule c1 t1, term_rule c2 t2 => (c1 == c2) && (t1 == t2)
  | sort_le c1 t1 t1', sort_le c2 t2 t2' =>
    (c1 == c2) && (t1 == t2) && (t1' == t2')
  | term_le c1 e1 e1' t1, term_le c2 e2 e2' t2 =>
    (c1 == c2) && (e1 == e2) && (e1' == e2') && (t1 == t2)
  | _,_ => false
  end.

Lemma eq_ruleP r1 r2 : reflect (r1 = r2) (eq_rule r1 r2).
Proof using .
Admitted.

Definition rule_eqMixin := Equality.Mixin eq_ruleP.

Canonical rule_eqType := @Equality.Pack rule rule_eqMixin.

(* TODO: need shifts?
Definition rule_constr_shift n r :=
  match r with
  | {| c |- sort } => {| map (constr_shift n) c |- sort}
  | {| c |- t } => {| map (constr_shift n) c |- constr_shift n t}
  | {< c |- t1 <# t2 } =>
    {< map (constr_shift n) c
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

Lemma rule_constr_shift_inj r1 r2 n : r1 %%!n = r2 %%!n -> r1 = r2.
Proof.
  case: r1; case: r2 => //=;
  intro_to (@eq rule); inversion; f_equal;
  move: constr_shift_inj seq_constr_shift_inj; eauto. 
Qed.  
*)
