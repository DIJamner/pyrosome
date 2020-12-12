Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From Utils Require Import Utils.
From Named Require Import Exp.
Import Exp.Notations.
Require Import String.

(* terms form a category over sorts w/ (empty or constant?) Γ *)
Inductive rule : Type :=
| sort_rule :  ctx -> seq string (*explicit args*) -> rule
| term_rule :  ctx -> seq string (*explicit args*) -> sort -> rule
| sort_le : ctx -> sort -> sort -> rule
| term_le : ctx -> exp -> exp -> sort -> rule.

Definition lang := named_list rule.

Module Notations.

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

  
  Declare Scope arule_scope.
  Bind Scope arule_scope with rule.
  Bind Scope arule_scope with lang.
  Delimit Scope arule_scope with arule.

  (* TODO: is there a better way to do this that doesn't affect list parsing?
     Current approach leads to 'only printing' notations
   *)
Notation "# s e .. e'" :=
  (s, (cons e' .. (cons e nil) ..))%string
  (in custom constr_conclusion at level 50,
      s constr at level 0, e constr at level 0, e' constr at level 0,
      format "# s  e  ..  e'"
  ).

Notation "# s" := (s, @nil string)%string
  (in custom constr_conclusion at level 50,
   s constr at level 0, format "# s").


Notation "'[s|' G ----------------------------------------------- cc 'srt' ]" :=
  (fst cc, sort_rule G (snd cc))
    (cc custom constr_conclusion at level 100,
     G custom ctx at level 100,
     format "'[' [s|  '[' G '//' ----------------------------------------------- '//' cc  'srt' ']' '//' ] ']'")
  : arule_scope.


Notation "'[s|' G ----------------------------------------------- # n 'srt' ]" :=
  (n%string, sort_rule G [::])
    (n constr at level 0,
     G custom ctx at level 100,
     format "'[' [s|  '[' G '//' ----------------------------------------------- '//' # n  'srt' ']' '//' ] ']'",
    only printing)
  : arule_scope.


Notation "'[s|' G ----------------------------------------------- # n a .. a' 'srt' ]" :=
  (n%string, sort_rule G (cons a' .. (cons a nil) .. )%string)
    (n constr at level 0,
     G custom ctx at level 100,
     a constr at level 0, a' constr at level 0,
     format "'[' [s|  '[' G '//' ----------------------------------------------- '//' # n  a  ..  a'  'srt' ']' '//' ] ']'", only printing)
  : arule_scope.

Check [s| "x" : #"env", "y" : #"ty" %"x", "z" : #"ty" %"x"
          -----------------------------------------------
          #"foo" "y" "z" srt                    ]%arule.

Eval compute in
    [s| "x" : #"env", "y" : #"ty" %"x", "z" : #"ty" %"x"
          -----------------------------------------------
                      #"foo" "y" "z" srt                    ]%arule.

Check [s| 
          -----------------------------------------------
            #"env" srt                    ]%arule.


Eval compute in
    [s| 
          -----------------------------------------------
            #"env" srt                    ]%arule.

          
Notation "[:| G ----------------------------------------------- cc : t ]" :=
  (fst cc, term_rule G (snd cc) t)
    (cc custom constr_conclusion at level 100,
     G custom ctx at level 100, t custom sort at level 100,
     format "'[' [:|  '[' G '//' ----------------------------------------------- '//' '[' cc  '/' :  t ']' ']' '//' ] ']'") : arule_scope.

Notation "'[:|' G ----------------------------------------------- # n : t ]" :=
  (n%string, term_rule G [::] t)
    (n constr at level 0,
     G custom ctx at level 100, t custom sort at level 100,
     format "'[' [:|  '[' G '//' ----------------------------------------------- '//' # n  :  t ']' '//' ] ']'",
    only printing)
  : arule_scope.


Notation "'[:|' G ----------------------------------------------- # n a .. a' : t ]" :=
  (n%string, term_rule G (cons a' .. (cons a nil) .. )%string t)
    (n constr at level 0,
     a constr at level 0, a' constr at level 0,
     G custom ctx at level 100, t custom sort at level 100,
     format "'[' [:|  '[' G '//' ----------------------------------------------- '//' # n  a  ..  a'  :  t ']' '//' ] ']'", only printing)
  : arule_scope.

Check [:| "G" : #"env",
          "A" : #"ty" %"G",
          "B" : #"ty" %"x",
          "e" : #"el" (#"wkn" %"A" %"B")
          -----------------------------------------------
          #"lam" "A" "e" : #"el" (#"->" %"A" %"B")]%arule.

Eval compute in
     [:| "G" : #"env",
          "A" : #"ty" %"G",
          "B" : #"ty" %"x",
          "e" : #"el" (#"wkn" %"A" %"B")
          -----------------------------------------------
          #"lam" "A" "e" : #"el" (#"->" %"A" %"B")]%arule.

Check [:|
          -----------------------------------------------
                      #"emp" : #"env"                   ]%arule.

Eval compute in
     [:|
          -----------------------------------------------
                      #"emp" : #"env"                   ]%arule.

Check [:| "G" : #"env",
           "A" : #"ty" %"G",
           "B" : #"ty" %"x",
           "e" : #"el" (#"wkn" %"A" %"B")
           -----------------------------------------------
           #"lam" "e" : #"el" (#"->" %"A" %"B") ]%arule.

Notation "'[s>' G ----------------------------------------------- ( s ) e1 = e2 ]" :=
  (s%string, sort_le G e1 e2)
    (s constr at level 0, G custom ctx at level 100,
     e1 custom sort at level 100, e2 custom sort at level 100,
     format "'[' [s>  '[' G '//' -----------------------------------------------  ( s ) '//' '[' e1 '/'  =  e2 ']' ']' '//' ] ']'")
  : arule_scope.


Check [s> "G" : #"env", "A" : #"ty" %"G", "B" : #"ty" %"G",
          "eq" : #"ty_eq" %"G" %"A" %"B" 
          ----------------------------------------------- ("ty_eq_sort")
          #"ty" %"G" %"A" = #"ty" %"G" %"B"
      ]%arule.
           
Notation "[:> G ----------------------------------------------- ( s ) e1 = e2 : t ]" :=
  (s%string, term_le G e1 e2 t)
    (s constr at level 0, G custom ctx at level 100,
     t custom sort at level 100,
     e1 custom exp at level 100, e2 custom exp at level 100, 
     format "'[' [:>  '[' G '//' -----------------------------------------------  ( s ) '//' '[' e1 '/'  =  e2 ']' '/'  :  t ']' '//' ] ']'")
  : arule_scope.


Check [:> "G" : #"env", "A" : #"ty" %"G", "B" : #"ty" %"G",
          "eq" : #"ty_eq" %"G" %"A" %"B" 
          ----------------------------------------------- ("ty_eq_sort")
          %"A" = %"B" : #"ty" %"G"
      ]%arule.

End Notations.

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
*)

Definition eq_rule r1 r2 : bool :=
  match r1, r2 with
  | sort_rule c1 args1, sort_rule c2 args2 => (c1 == c2) && (args1 == args2)
  | term_rule c1 args1 t1, term_rule c2 args2 t2 =>
    (c1 == c2) && (args1 == args2) && (t1 == t2)
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

