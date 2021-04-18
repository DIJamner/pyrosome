Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import List String.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Exp.
(*TODO: why does this generate warnings?*)
Import Exp.Notations.

Inductive rule : Set :=
| sort_rule :  ctx -> list string (*explicit args*) -> rule
| term_rule :  ctx -> list string (*explicit args*) -> sort -> rule
| sort_eq_rule : ctx -> sort -> sort -> rule
| term_eq_rule : ctx -> exp -> exp -> sort -> rule.
#[export] Hint Constructors rule : exp.

Definition lang := named_list rule.

Lemma invert_eq_sort_rule_sort_rule c c' args args'
  : sort_rule c args = sort_rule c' args' <-> c = c' /\ args = args'.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_sort_rule_sort_rule : exp.
  
Lemma invert_eq_sort_rule_term_rule c c' args args' t'
  : sort_rule c args = term_rule c' args' t' <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_sort_rule_term_rule : exp.

Lemma invert_eq_sort_rule_sort_eq_rule c c' args t1' t2'
  : sort_rule c args = sort_eq_rule c' t1' t2' <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_sort_rule_sort_eq_rule : exp.

Lemma invert_eq_sort_rule_term_eq_rule c c' args e1' e2' t
  : sort_rule c args = term_eq_rule c' e1' e2' t <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_sort_rule_term_eq_rule : exp.
  
Lemma invert_eq_term_rule_sort_rule c c' args args' t
  : term_rule c args t = sort_rule c' args' <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_term_rule_sort_rule : exp.

Lemma invert_eq_term_rule_term_rule c c' args args' t t'
  : term_rule c args t = term_rule c' args' t' <-> c = c' /\ args = args' /\ t = t'.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_term_rule_term_rule : exp.

Lemma invert_eq_term_rule_sort_eq_rule c c' args t t1' t2'
  : term_rule c args t = sort_eq_rule c' t1' t2' <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_term_rule_sort_eq_rule : exp.

Lemma invert_eq_term_rule_term_eq_rule c c' args t e1' e2' t'
  : term_rule c args t = term_eq_rule c' e1' e2' t' <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_term_rule_term_eq_rule : exp.


Lemma invert_eq_sort_eq_rule_sort_rule c c' args' t1 t2
  : sort_eq_rule c t1 t2 = sort_rule c' args' <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_sort_eq_rule_sort_rule : exp.

Lemma invert_eq_sort_eq_rule_term_rule c c' args' t1 t2 t'
  : sort_eq_rule c t1 t2 = term_rule c' args' t' <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_sort_eq_rule_term_rule : exp.

Lemma invert_eq_sort_eq_rule_sort_eq_rule c c' t1 t1' t2 t2'
  : sort_eq_rule c t1 t2 = sort_eq_rule c' t1' t2' <-> c = c' /\ t1 = t1' /\ t2 = t2'.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_sort_eq_rule_sort_eq_rule : exp.

Lemma invert_eq_sort_eq_rule_term_eq_rule c c' t1 t2 e1' e2' t'
  : sort_eq_rule c t1 t2 = term_eq_rule c' e1' e2' t' <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_sort_eq_rule_term_eq_rule : exp.
  
Lemma invert_eq_term_eq_rule_sort_rule c c' e1 e2 args' t
  : term_eq_rule c e1 e2 t = sort_rule c' args' <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_term_eq_rule_sort_rule : exp.

Lemma invert_eq_term_eq_rule_term_rule c c' args' t e1 e2 t'
  : term_eq_rule c e1 e2 t = term_rule c' args' t' <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_term_eq_rule_term_rule : exp.

Lemma invert_eq_term_eq_rule_sort_eq_rule c c' e1 e2 t t1' t2'
  : term_eq_rule c e1 e2 t = sort_eq_rule c' t1' t2' <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_term_eq_rule_sort_eq_rule : exp.

Lemma invert_eq_term_eq_rule_term_eq_rule c c' e1 e2 e1' e2' t t'
  : term_eq_rule c e1 e2 t = term_eq_rule c' e1' e2' t' <-> c = c' /\ e1 = e1' /\ e2 = e2' /\ t = t'.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_term_eq_rule_term_eq_rule : exp.


(*Moved out of the module because Coq seems
  to include them at the the top level anyway
 *)
Declare Custom Entry constr_conclusion.

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
  
  Declare Scope arule_scope.
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
  (n%string, sort_rule G [])
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
  (n%string, term_rule G [] t)
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
  (s%string, sort_eq_rule G e1 e2)
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
  (s%string, term_eq_rule G e1 e2 t)
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


Definition ws_rule r : Prop :=
  match r with
  | sort_rule c args => sublist args (map fst c) /\ ws_ctx c
  | term_rule c args t => sublist args (map fst c) /\ (ws_ctx c) /\ (well_scoped (map fst c) t)
  | sort_eq_rule c t t'=>
    (ws_ctx c) /\ (well_scoped (map fst c) t)
    /\ (well_scoped (map fst c) t')
  | term_eq_rule c e e' t =>
    (ws_ctx c) /\ (well_scoped (map fst c) e)
    /\ (well_scoped (map fst c) e') /\ (well_scoped (map fst c) t)
  end.

Definition ws_lang (l : lang) : Prop :=
  (all_fresh l) /\ (all ws_rule (map snd l)).

Arguments ws_lang !l/.

Lemma rule_in_ws l n r : ws_lang l -> In (n,r) l -> ws_rule r.
Proof using .
  induction l; 
    basic_goal_prep;
    basic_exp_crush.
Qed.

Lemma reconstruct_ws_lang l
  : all_fresh l /\ all ws_rule (map snd l) -> ws_lang l.
Proof.
  eauto.
Qed.
#[export] Hint Resolve reconstruct_ws_lang : exp.

Lemma ws_lang_all_ws_rule l
  : ws_lang l -> all ws_rule (map snd l).
Proof.
  unfold ws_lang; intuition.
Qed.
#[export] Hint Resolve ws_lang_all_ws_rule : exp.
