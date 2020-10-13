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

Notation "# c ( bd , .. , bd' )" :=
  (con c%string (cons bd' .. (cons bd nil) ..))
    (in custom expr at level 0, c constr at level 0,
    bd custom subst_binding, bd' custom subst_binding).

Notation "e / x" :=
  (x%string,e) (in custom subst_binding at level 0,
        e custom expr, x constr at level 0).

Notation "# c" :=
  (con c%string [::])
    (in custom expr at level 0, c constr at level 0).

Notation "# c ( bd , .. , bd' )" :=
  (srt c%string (cons bd' .. (cons bd nil) ..))
    (in custom srt at level 0, c constr at level 0,
    bd custom subst_binding, bd' custom subst_binding).

Notation "x" :=
  x (in custom expr at level 0, x ident).
Notation "x" :=
  x (in custom srt at level 0, x ident).
Notation "x" :=
  x (in custom subst at level 0, x ident).
Notation "x" :=
  x (in custom ctx at level 0, x ident).
               
Notation "# c" :=
  (srt c%string [::])
    (in custom srt at level 0, c constr at level 0).

Notation "[:> G '|-s' s ]" :=
  (s%string, sort_rule G)
    (s constr at level 0, G custom ctx,
    format "'[v  ' [:> G '/' '|-s' s ] ']'").

Notation "[:> G |- s : t ]" :=
  (s%string, term_rule G t)
    (t custom srt,
     s constr at level 0, G custom ctx,
    format "'[v  ' [:> G '/' |- '[  ' s '/' : t ']' ] ']'").

Notation "[:> G '|-s' e1 = e2 ( s ) ]" :=
  (s%string, sort_le G e1 e2)
    (at level 99,
     s constr at level 0, G custom ctx,
     e1 custom srt, e2 custom srt).

Notation "[:> G |- e1 = e2 : t ( s ) ]" :=
  (s%string, term_le G e1 e2 t)
    (at level 98,
     s constr at level 0, G custom ctx,
     t custom srt, e1 custom expr, e2 custom expr).


Notation "(:)" := [::] (in custom ctx).

Notation "[:> '|-s' s ]" :=
  [:> (:) |-s s ]
    (s constr at level 0, format "'[v  ' [:> '|-s' s ] ']'").

Notation "[:> |- s : t ]" :=
  [:> (:) |- s : t ]
    (at level 97, t custom srt,
     s constr at level 0,
    format "'[v  ' [:> |- '[  ' s '/' : t ']' ] ']'").

Notation "[:> '|-s' e1 = e2 ( s ) ]" :=
  [:> (:) |-s e1 = e2 (s)]
    (at level 97, s constr at level 0,
     e1 custom srt, e2 custom srt).

(*TODO: fix
Notation "[:> |- e1 = e2 : t ( s ) ]" :=
  [:> (:) |- e1 = e2 : t (s)]
    (at level 96, s constr at level 0,
     t custom srt, e1 custom expr, e2 custom expr).
*)

(*Notation "[:> |- rc ]" :=
  (rc [::])
    (rc custom rule_conclusion at level 99).*)

(*

Notation "s 'sort'" :=
  (fun G => (s%string, sort_rule G))
    (in custom rule_conclusion at level 98, s constr at level 0).
Notation "s : t" :=
  (fun G => (s%string, term_rule G t))
    (in custom rule_conclusion at level 98, t custom srt, s constr at level 0).
Print Custom Grammar rule_conclusion.
*)
(*
Notation " G |- t = t' ( s )" :=
  (s%string, sort_le G t t')
    (in custom rule at level 96, G custom ctx, t custom srt, t' custom srt).

Notation " G |- e = e' : t ( s )" :=
  (s%string, term_le G e e' t)
    (in custom rule at level 95, G custom ctx, t custom srt, e custom expr, e' custom expr).

Notation " |- s 'sort'" :=
  (s%string, sort_rule [::])
    (in custom rule at level 98, s constr).

Notation " |- s : t" :=
  (s%string, term_rule [::] t)
    (in custom rule at level 97, t custom srt).

Notation " |- (s) t = t' sort" :=
  (s%string, sort_le [::] t t')
    (in custom rule at level 96, t custom srt, t' custom srt).

Notation " |- (s) e = e' : t" :=
  (s%string, term_le [::] e e' t)
    (in custom rule at level 95, t custom srt, e custom expr, e' custom expr).
*)
Notation "(:)" := [::] (in custom ctx).

Notation "'ERR'" := nil (in custom srt at level 0).

Check [:> (:)|- "foo" : #"bar" (#"baz"/"e", #"qux"/"f")].
(*TODO: get printing working! are list notations interfering?*)

Notation "s : t" :=
  [::(s%string,t)]
    (in custom ctx at level 20, t custom srt).

Notation "G , s : t" :=
  ((s%string,t)::G)
    (in custom ctx at level 30,
        G custom ctx, t custom srt).


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
