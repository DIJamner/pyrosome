Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Require Import String.
From Utils Require Import Utils.
From Named Require Import Exp.
Import Exp.Notations.

(* terms form a category over sorts w/ (empty or constant?) Γ *)
Inductive rule : Type :=
| sort_rule :  ctx -> rule
| term_rule :  ctx -> sort -> rule
| sort_le : ctx -> sort -> sort -> rule
| term_le : ctx -> exp -> exp -> sort -> rule.

Definition lang := named_list rule.

Module Notations.
(*
(* TODO: get rule bar printing to work *)
Inductive rule_bar := bar_base | bar_ext (r : rule_bar).

Declare Custom Entry rule_dash.
Notation "-" := bar_ext (in custom rule_dash at level 0).

Notation "x .. y":=
  (x .. (y bar_base) ..) (in custom rule_bar at level 50,
                      x custom rule_dash at level 100,
                      y custom rule_dash at level 100).

Definition with_rule_bar' (rb : nat) := 0.

Notation "'[TMP' rb ]" :=
 rb
    (at level 0, rb custom rule_bar at level 100).
Check [TMP ------------------------------------------------].

Definition with_rule_bar (rb : rule_bar) (r : string*rule) := r.
 *)

  
  Declare Scope rule_scope.
  Bind Scope rule_scope with rule.
  Bind Scope rule_scope with lang.
  Delimit Scope rule_scope with rule.

Notation "'[s|' G ----------------------------------------------- # name 'srt' ]" :=
  (name%string, sort_rule G)
    (name constr at level 0,
     G custom ctx at level 100,
     format "'[' [s|  '[' G '//' ----------------------------------------------- '//' # name  'srt' ']' '//' ] ']'")
  : rule_scope.

Check [s| "x" : #"env", "y" : #"ty" %"x", "z" : #"ty" %"x"
          -----------------------------------------------
                      #"foo" srt                    ]%rule.

Check [s| 
          -----------------------------------------------
                      #"env" srt                    ]%rule.

          
Notation "[:| G ----------------------------------------------- name : t ]" :=
  (name%string, term_rule G t)
    (name constr at level 0,
     G custom ctx at level 100, t custom sort at level 100,
     format "'[' [:|  '[' G '//' ----------------------------------------------- '//' '[' name  '/' :  t ']' ']' '//' ] ']'")
  : rule_scope.

Check [:| "G" : #"env",
          "A" : #"ty" %"G",
          "B" : #"ty" %"x",
          "e" : #"el" (#"wkn" %"A" %"B")
          -----------------------------------------------
          "lam" : #"el" (#"->" %"A" %"B")]%rule.

Check [:|
          -----------------------------------------------
                      "emp" : #"env"                   ]%rule.


Check [:| "G" : #"env",
           "A" : #"ty" %"G",
           "B" : #"ty" %"x",
           "e" : #"el" (#"wkn" %"A" %"B")
           -----------------------------------------------
           "lam" : #"el" (#"->" %"A" %"B") ]%rule.

Notation "'[s>' G ----------------------------------------------- ( s ) e1 = e2 ]" :=
  (s%string, sort_le G e1 e2)
    (s constr at level 0, G custom ctx at level 100,
     e1 custom sort at level 100, e2 custom sort at level 100,
     format "'[' [s>  '[' G '//' -----------------------------------------------  ( s ) '//' '[' e1 '/'  =  e2 ']' ']' '//' ] ']'")
  : rule_scope.


Check [s> "G" : #"env", "A" : #"ty" %"G", "B" : #"ty" %"G",
          "eq" : #"ty_eq" %"G" %"A" %"B" 
          ----------------------------------------------- ("ty_eq_sort")
          #"ty" %"G" %"A" = #"ty" %"G" %"B"
      ]%rule.
           
Notation "[:> G ----------------------------------------------- ( s ) e1 = e2 : t ]" :=
  (s%string, term_le G e1 e2 t)
    (s constr at level 0, G custom ctx at level 100,
     t custom sort at level 100,
     e1 custom exp at level 100, e2 custom exp at level 100, 
     format "'[' [:>  '[' G '//' -----------------------------------------------  ( s ) '//' '[' e1 '/'  =  e2 ']' '/'  :  t ']' '//' ] ']'")
  : rule_scope.

Check [:> "G" : #"env", "A" : #"ty" %"G", "B" : #"ty" %"G",
          "eq" : #"ty_eq" %"G" %"A" %"B" 
          ----------------------------------------------- ("ty_eq_sort")
          %"A" = %"B" : #"ty" %"G"
      ]%rule.

(* TODO: do I still want to allow these notations? I think so.
   If so, which by default? For now there are only parsing.
   Can prob. handle better once I fix rule bars
*)

Notation "'[s|' G |- s ]" :=
  (s%string, sort_rule G)
    (s constr at level 0, G custom ctx, only parsing
    (*    format "'[  ' G '/' '|-s' s ']'").*))
: rule_scope.

Notation "[:| G |- s : t ]" :=
  (s%string, term_rule G t)
    (t custom sort,
     s constr at level 0, G custom ctx, only parsing
    (*format "'[  ' G '/' |- '[  ' s '/' : t ']' ']'"*))
  : rule_scope.

Notation "'[s>' G |- ( s ) e1 = e2 ]" :=
  (s%string, sort_le G e1 e2)
    (s constr at level 0, G custom ctx,
     e1 custom sort, e2 custom sort, only parsing)
: rule_scope.

Notation "[:> G |- ( s ) e1 = e2 : t ]" :=
  (s%string, term_le G e1 e2 t)
    (s constr at level 0, G custom ctx,
     t custom sort, e1 custom exp, e2 custom exp, only parsing)
  : rule_scope.

Check [:| "x" : #"foo", "y" : #"bar" |- "foo" : #"bar" #"baz" #"qux"]%rule.
Check [s> |- ("eq")#"foo" = #"bar"]%rule.
End Notations.


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
  destruct r1; destruct r2; simpl; solve_reflect_norec.
Qed.

Definition rule_eqMixin := Equality.Mixin eq_ruleP.

Canonical rule_eqType := @Equality.Pack rule rule_eqMixin.


Definition ws_rule r : bool :=
  match r with
  | sort_rule c => ws_ctx c
  | term_rule c t => (ws_ctx c) && (well_scoped (map fst c) t)
  | sort_le c t t'=>
    (ws_ctx c) && (well_scoped (map fst c) t)
    && (well_scoped (map fst c) t')
  | term_le c e e' t =>
    (ws_ctx c) && (well_scoped (map fst c) e)
    && (well_scoped (map fst c) e') && (well_scoped (map fst c) t)
  end.

Definition ws_lang (l : lang) : bool :=
  (all_fresh l) && (all ws_rule (map snd l)).

Arguments ws_lang !l/.

Lemma rule_in_ws l n r : ws_lang l -> (n,r) \in l -> ws_rule r.
Proof using .
  elim: l; intros; break; simpl in *; break; auto.
  match goal with [H : is_true(_ \in _::_)|- _]=>
                  move: H;rewrite in_cons; move /orP => [] end.
  {
    move /eqP => []; intros; by subst.
  }
  {
    apply H; unfold ws_lang; break_goal; auto.
  }
Qed.
