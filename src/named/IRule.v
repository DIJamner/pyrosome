Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

From Utils Require Import Utils.
From Named Require Import IExp.
Require Import String.

(* terms form a category over sorts w/ (empty or constant?) Γ *)
Inductive rule : Type :=
| sort_rule :  ctx -> seq string -> seq string -> rule
| term_rule :  ctx -> seq string -> seq string -> seq string -> seq string -> sort -> rule
| sort_le : ctx -> sort -> sort -> rule
| term_le : ctx -> exp -> exp -> sort -> rule.


Declare Custom Entry exp.
Declare Custom Entry sort.
Declare Custom Entry subst.
Declare Custom Entry ctx.

Declare Custom Entry subst_binding.

(*TODO: rename *)
Definition scon := srt.

(*
Notation "e / x" :=
  (x%string,e) (in custom subst_binding at level 0,
        e custom expr, x constr at level 0).*)

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

Notation "! x" :=
  x (in custom exp at level 0, x ident).
Notation "! x" :=
  x (in custom sort at level 0, x ident).
Notation "! x" :=
  x (in custom subst at level 0, x ident).
Notation "! x" :=
  x (in custom ctx at level 0, x ident).

Declare Custom Entry ctx_binding.

Notation "bd , .. , bd'" :=
  (cons bd' .. (cons bd nil)..)
    (in custom ctx at level 100, bd custom ctx_binding at level 100,
    format "'[hv' bd , '/' .. , '/' bd' ']'").

Notation "(:)" := (@nil (string*string*sort)) (in custom ctx at level 0).

Notation "x <= t" :=
  (None (*not synth*), (x%string, t))
    (in custom ctx_binding at level 100, x constr at level 0,
        t custom sort at level 100).

Notation "x => t" :=
  (Some x%string (*synth*), (x%string, t))
    (in custom ctx_binding at level 100, x constr at level 0,
        t custom sort at level 100).

Notation "'{{c' e }}" := (e) (at level 0,e custom ctx at level 100).

Check {{c (:) }}.
Check {{c "x" <= #"env"}}.
Check {{c "x" <= #"env", "y" => #"ty" %"x", "z" <= #"ty" %"x"}}.

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

(*TODO: move to utils*)
Fixpoint filter_map {A B} (f : A -> option B) l :=
  match l with
  | [::] => [::]
  | e::l' =>
    match f e with
    | Some e' => e'::(filter_map f l')
    | None => filter_map f l'
    end
  end.

Notation "'[s|' G
                ----------------------------------------------- 
                s e .. e' 'srt' ]" :=
  (s%string, sort_rule (map snd G) (filter_map fst G)
                       (cons e' .. (cons e nil) ..)%string )
    (s constr at level 0, e constr at level 0, e' constr at level 0,
     G custom ctx at level 100,
     format "'[' [s| 
'[' G '//'
----------------------------------------------- '//'
s e .. e'  'srt' ']' '//'
 ] ']'").

Check [s| "x" <= #"env", "y" => #"ty" %"x", "z" <= #"ty" %"x"
          -----------------------------------------------
                      "foo" "y" "z" srt                    ].

          
Notation "[:| G 
              -----------------------------------------------    
              s e .. e' : t ]" :=
  (s%string, term_rule (map snd G) (filter_map fst G)
                       (cons e' .. (cons e nil) ..)%string
                       (filter_map fst G)
                       (cons e' .. (cons e nil) ..)%string t)
    (s constr at level 0, e constr at level 0, e' constr at level 0,
     G custom ctx at level 100, t custom sort at level 100,
     format "'[' [:| 
'[' G '//'
----------------------------------------------- '//'
'[' s e .. e'  '/' :  t ']' ']' '//'
 ] ']'").

Check [:| "G" <= #"env",
          "A" <= #"ty" %"G",
          "B" <= #"ty" %"x",
          "e" => #"el" (#"wkn" %"A" %"B")
          -----------------------------------------------
          "lam" "A" "e" : #"el" (#"->" %"A" %"B")].

Definition constr_name_eq (c1 c2 : string) r : string * rule :=
  if String.eqb c1 c2 then r
  else ("ERR: constr names differ"%string, snd r).

Declare Custom Entry synth_ctx.
Declare Custom Entry synth_ctx_binding.

Notation "bd , .. , bd'" :=
  (cons bd' .. (cons bd nil)..)
    (in custom synth_ctx at level 100, bd custom synth_ctx_binding at level 100,
    format "'[hv' bd , '/' .. , '/' bd' ']'").

Notation "(:)" := (@nil string) (in custom synth_ctx at level 0).


Notation "x =>" := x%string (*synth*)
    (in custom synth_ctx_binding at level 100, x constr at level 0).


Notation "[<=| G 
              -----------------------------------------------    
              s e .. e' <= t
           =>| Gs
              -----------------------------------------------    
              ss es .. es' => ]" :=
  (constr_name_eq s ss
                 (s%string, term_rule (map snd G) (filter_map fst G)
                       (cons e' .. (cons e nil) ..)%string
                       Gs
                       (cons es' .. (cons es nil) ..)%string t))
    (s constr at level 0, e constr at level 0, e' constr at level 0,
     G custom ctx at level 100, t custom sort at level 100,
     ss constr at level 0, es constr at level 0, es' constr at level 0,
     Gs custom synth_ctx at level 100,
     format "'[' [<=| 
'[' G '//'
----------------------------------------------- '//'
'[' s e .. e'  '/' <=  t ']' ']' '//'
=>| '[' Gs '//'
----------------------------------------------- '//'
'[' ss es .. es'  '/' => ']' ']' '//'
 ] ']'").


Check [<=| "G" <= #"env",
           "A" <= #"ty" %"G",
           "B" <= #"ty" %"x",
           "e" => #"el" (#"wkn" %"A" %"B")
           -----------------------------------------------
           "lam" "e" <= #"el" (#"->" %"A" %"B")
       =>| "e" =>
           -----------------------------------------------
           "lam" "A" "e" =>].

Notation "[=>| G 
              -----------------------------------------------    
              s e .. e' => t
           <=| Gs
              -----------------------------------------------    
              ss es .. es' <= ]" :=
  (constr_name_eq s ss
                 (s%string, term_rule (map snd G) Gs
                                      (cons es' .. (cons es nil) ..)%string
                                       (filter_map fst G)
                       (cons e' .. (cons e nil) ..)%string t))
    (s constr at level 0, e constr at level 0, e' constr at level 0,
     G custom ctx at level 100, t custom sort at level 100,
     ss constr at level 0, es constr at level 0, es' constr at level 0,
     Gs custom synth_ctx at level 100,
     format "'[' [=>| 
'[' G '//'
----------------------------------------------- '//'
'[' s e .. e'  '/' =>  t ']' ']' '//'
<=| '[' Gs '//'
----------------------------------------------- '//'
'[' ss es .. es'  '/' <= ']' ']' '//'
 ] ']'").


Check [=>| "G" <= #"env",
           "A" <= #"ty" %"G",
           "B" <= #"ty" %"x",
           "e" => #"el" (#"wkn" %"A" %"B")
           -----------------------------------------------
           "lam" "A" "e" => #"el" (#"->" %"A" %"B")
       <=| "e" =>
           -----------------------------------------------
           "lam" "e" <=].

Notation "'[s>' G rb ( s ) e1 = e2 ]" :=
  (snd (rb,(s%string, sort_le G e1 e2)))
    (s constr at level 0, G custom ctx,
     e1 custom srt, e2 custom srt, rb custom rule_bar).

Notation "[:> G rb ( s ) e1 = e2 : t ]" :=
  (snd (rb, (s%string, term_le G e1 e2 t)))
    (s constr at level 0, G custom ctx,
     t custom srt, e1 custom exp, e2 custom exp, rb custom rule_bar).

Notation "'[s|' rb s ]" :=
  (snd (rb, (s%string, sort_rule [::])))
    (s constr at level 0, rb custom rule_bar).

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
