Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From Utils Require Import Utils.
From Named Require Import Exp.
Require Import String.

(* terms form a category over sorts w/ (empty or constant?) Γ *)
Inductive rule : Type :=
| sort_rule :  ctx -> seq string (*explicit args*) -> rule
| term_rule :  ctx -> seq string (*explicit args*) -> sort -> rule
| sort_le : ctx -> sort -> sort -> rule
| term_le : ctx -> exp -> exp -> sort -> rule.

(*TODO: rename *)
Definition scon := srt.

(* TODO: notations *)
(*
Notation "e / x" :=
  (x%string,e) (in custom subst_binding at level 0,
        e custom expr, x constr at level 0).*)
(*
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
  | srt c l => srt c (e'::l)
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

Notation "'{{e' e }}" := (e) (at level 0,e custom exp at level 100).
Notation "'{{s' e }}" := (e) (at level 0,e custom sort at level 100).

Notation "% x" :=
  (var x%string)
    (in custom exp at level 0, x constr at level 0, format "% x").


Check {{e #"foo" }}.
Check {{e #"foo" (#"bar" %"x") #"baz" %"y"}}.
Check {{s #"foo" }}.
Check {{s #"foo" (#"bar" %"x") #"baz" %"y"}}.

(*
Notation "! x" :=
  x (in custom exp at level 0, x ident).
Notation "! x" :=
  x (in custom sort at level 0, x ident).
Notation "! x" :=
  x (in custom subst at level 0, x ident).
Notation "! x" :=
  x (in custom ctx at level 0, x ident).
*)

Declare Custom Entry ctx.
Declare Custom Entry ctx_binding.

Definition print_ctx (c : list (string*sort)) := c.

Notation "bd , .. , bd'" :=
  (print_ctx (cons bd' .. (cons bd nil)..))
    (in custom ctx at level 100, bd custom ctx_binding at level 100,
    format "'[hv' bd ,  '/' .. ,  '/' bd' ']'").

Notation "(:)" := (@nil (string*sort)) (in custom ctx at level 0).

Notation "x : t" :=
  (x%string, t)
    (in custom ctx_binding at level 100, x constr at level 0,
        t custom sort at level 100).

Notation "'{{c' e }}" := (e) (at level 0,e custom ctx at level 100).

Check {{c (:) }}.
Check {{c "x" : #"env"}}.
Check {{c "x" : #"env", "y" : #"ty" %"x", "z" : #"ty" %"x"}}.

(*
(* TODO: get rule bar printing to work *)
Inductive rule_bar := bar_base | bar_ext (r : rule_bar).

Declare Custom Entry rule_bar.
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

Declare Custom Entry constr_conclusion.
Notation "s e .. e'" :=
  (s, (cons e' .. (cons e nil) ..))%string
  (in custom constr_conclusion at level 50,
   s constr at level 0, e constr at level 0, e' constr at level 0).

Notation "s" := (s, @nil string)%string
  (in custom constr_conclusion at level 50,
   s constr at level 0).


Notation "'[s|' G ----------------------------------------------- cc 'srt' ]" :=
  (fst cc, sort_rule G (snd cc))
    (cc custom constr_conclusion at level 100,
     G custom ctx at level 100,
     format "'[' [s|  '[' G '//' ----------------------------------------------- '//' cc  'srt' ']' '//' ] ']'").

Check [s| "x" : #"env", "y" : #"ty" %"x", "z" : #"ty" %"x"
          -----------------------------------------------
                      "foo" "y" "z" srt                    ].

Check [s| (:)
          -----------------------------------------------
                      "env" srt                    ].

          
Notation "[:| G ----------------------------------------------- cc : t ]" :=
  (fst cc, term_rule G (snd cc) t)
    (cc custom constr_conclusion at level 100,
     G custom ctx at level 100, t custom sort at level 100,
     format "'[' [:|  '[' G '//' ----------------------------------------------- '//' '[' cc  '/' :  t ']' ']' '//' ] ']'").

Check [:| "G" : #"env",
          "A" : #"ty" %"G",
          "B" : #"ty" %"x",
          "e" : #"el" (#"wkn" %"A" %"B")
          -----------------------------------------------
          "lam" "A" "e" : #"el" (#"->" %"A" %"B")].

Check [:| (:)
          -----------------------------------------------
                      "emp" : #"env"                   ].



Notation "[:| G ----------------------------------------------- cc : t ]" :=
  (fst cc, term_rule G (snd cc) t)
    (cc custom constr_conclusion at level 100,
     G custom ctx at level 100, t custom sort at level 100,
     format "'[' [:|  '[' G '//' ----------------------------------------------- '//' '[' cc  '/' :  t ']' ']' '//' ] ']'").


Check [:| "G" : #"env",
           "A" : #"ty" %"G",
           "B" : #"ty" %"x",
           "e" : #"el" (#"wkn" %"A" %"B")
           -----------------------------------------------
           "lam" "e" : #"el" (#"->" %"A" %"B") ].

Notation "'[s>' G ----------------------------------------------- ( s ) e1 = e2 ]" :=
  (s%string, sort_le G e1 e2)
    (s constr at level 0, G custom ctx at level 100,
     e1 custom sort at level 100, e2 custom sort at level 100,
    format "'[' [s>  '[' G '//' -----------------------------------------------  ( s ) '//' '[' e1 '/'  =  e2 ']' ']' '//' ] ']'").


Check [s> "G" : #"env", "A" : #"ty" %"G", "B" : #"ty" %"G",
          "eq" : #"ty_eq" %"G" %"A" %"B" 
          ----------------------------------------------- ("ty_eq_sort")
          #"ty" %"G" %"A" = #"ty" %"G" %"B"
      ].
           
Notation "[:> G ----------------------------------------------- ( s ) e1 = e2 : t ]" :=
  (s%string, term_le G e1 e2 t)
    (s constr at level 0, G custom ctx at level 100,
     t custom sort at level 100,
     e1 custom exp at level 100, e2 custom exp at level 100, 
    format "'[' [:>  '[' G '//' -----------------------------------------------  ( s ) '//' '[' e1 '/'  =  e2 ']' '/'  :  t ']' '//' ] ']'").


Check [:> "G" : #"env", "A" : #"ty" %"G", "B" : #"ty" %"G",
          "eq" : #"ty_eq" %"G" %"A" %"B" 
          ----------------------------------------------- ("ty_eq_sort")
          %"A" = %"B" : #"ty" %"G"
      ].
*)
Definition lang := named_list rule.
(*
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
 (* TODO:
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
*)*)

Parameter eq_rule : rule -> rule -> bool.
Lemma eq_ruleP r1 r2 : reflect (r1 = r2) (eq_rule r1 r2).
Proof using .
Admitted.

Definition rule_eqMixin := Equality.Mixin eq_ruleP.

Canonical rule_eqType := @Equality.Pack rule rule_eqMixin.

