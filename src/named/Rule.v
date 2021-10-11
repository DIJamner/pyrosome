Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import List String.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Term.
(*TODO: why does this generate warnings?*)
Import Term.Notations.
Import SumboolNotations.


Section WithVar.
  Context (V : Type)
          {V_Eqb : Eqb V}
          {V_default : WithDefault V}.

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).

Inductive rule :=
| sort_rule :  ctx -> list V (*explicit args*) -> rule
| term_rule :  ctx -> list V (*explicit args*) -> sort -> rule
| sort_eq_rule : ctx -> sort -> sort -> rule
| term_eq_rule : ctx -> term -> term -> sort -> rule.
Hint Constructors rule : term.

Instance default_rule : WithDefault rule := sort_rule [] [].

Definition lang := named_list rule.

Lemma invert_eq_sort_rule_sort_rule c c' args args'
  : sort_rule c args = sort_rule c' args' <-> c = c' /\ args = args'.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_sort_rule_sort_rule : term.

Lemma invert_eq_sort_rule_term_rule c c' args args' t'
  : sort_rule c args = term_rule c' args' t' <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_sort_rule_term_rule : term.


Lemma invert_eq_sort_rule_sort_eq_rule c c' args t1' t2'
  : sort_rule c args = sort_eq_rule c' t1' t2' <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_sort_rule_sort_eq_rule : term.

Lemma invert_eq_sort_rule_term_eq_rule c c' args e1' e2' t
  : sort_rule c args = term_eq_rule c' e1' e2' t <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_sort_rule_term_eq_rule : term.
  
Lemma invert_eq_term_rule_sort_rule c c' args args' t
  : term_rule c args t = sort_rule c' args' <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_term_rule_sort_rule : term.

Lemma invert_eq_term_rule_term_rule c c' args args' t t'
  : term_rule c args t = term_rule c' args' t' <-> c = c' /\ args = args' /\ t = t'.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_term_rule_term_rule : term.

Lemma invert_eq_term_rule_sort_eq_rule c c' args t t1' t2'
  : term_rule c args t = sort_eq_rule c' t1' t2' <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_term_rule_sort_eq_rule : term.

Lemma invert_eq_term_rule_term_eq_rule c c' args t e1' e2' t'
  : term_rule c args t = term_eq_rule c' e1' e2' t' <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_term_rule_term_eq_rule : term.

Lemma invert_eq_sort_eq_rule_sort_rule c c' args' t1 t2
  : sort_eq_rule c t1 t2 = sort_rule c' args' <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_sort_eq_rule_sort_rule : term.

Lemma invert_eq_sort_eq_rule_term_rule c c' args' t1 t2 t'
  : sort_eq_rule c t1 t2 = term_rule c' args' t' <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_sort_eq_rule_term_rule : term.

Lemma invert_eq_sort_eq_rule_sort_eq_rule c c' t1 t1' t2 t2'
  : sort_eq_rule c t1 t2 = sort_eq_rule c' t1' t2' <-> c = c' /\ t1 = t1' /\ t2 = t2'.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_sort_eq_rule_sort_eq_rule : term.

Lemma invert_eq_sort_eq_rule_term_eq_rule c c' t1 t2 e1' e2' t'
  : sort_eq_rule c t1 t2 = term_eq_rule c' e1' e2' t' <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_sort_eq_rule_term_eq_rule : term.
  
Lemma invert_eq_term_eq_rule_sort_rule c c' e1 e2 args' t
  : term_eq_rule c e1 e2 t = sort_rule c' args' <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_term_eq_rule_sort_rule : term.

Lemma invert_eq_term_eq_rule_term_rule c c' args' t e1 e2 t'
  : term_eq_rule c e1 e2 t = term_rule c' args' t' <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_term_eq_rule_term_rule : term.

Lemma invert_eq_term_eq_rule_sort_eq_rule c c' e1 e2 t t1' t2'
  : term_eq_rule c e1 e2 t = sort_eq_rule c' t1' t2' <-> False.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_term_eq_rule_sort_eq_rule : term.

Lemma invert_eq_term_eq_rule_term_eq_rule c c' e1 e2 e1' e2' t t'
  : term_eq_rule c e1 e2 t = term_eq_rule c' e1' e2' t' <-> c = c' /\ e1 = e1' /\ e2 = e2' /\ t = t'.
Proof. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_term_eq_rule_term_eq_rule : term.

Notation well_scoped := (@well_scoped V V_Eqb).

Definition ws_rule r : Prop :=
  match r with
  | sort_rule c args => sublist args (map fst c) /\ ws_ctx c
  | term_rule c args t => sublist args (map fst c) /\ (ws_ctx c)
                          /\ (well_scoped (map fst c) t)
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
    basic_term_firstorder_crush.
Qed.

Lemma reconstruct_ws_lang l
  : all_fresh l /\ all ws_rule (map snd l) -> ws_lang l.
Proof.
  eauto.
Qed.
Hint Resolve reconstruct_ws_lang : term.

Lemma ws_lang_all_ws_rule l
  : ws_lang l -> all ws_rule (map snd l).
Proof.
  unfold ws_lang; intuition.
Qed.
Hint Resolve ws_lang_all_ws_rule : term.


Definition rule_eq_dec (r1 r2 : rule) : {r1 = r2} + {~ r1 = r2}.
  refine(match r1, r2 with
         | sort_rule c args, sort_rule c' args' =>
           SB! (ctx_eq_dec c c') SB& (list_eq_dec Eqb_dec args args')
         | term_rule c args t, term_rule c' args' t' =>
           SB! (ctx_eq_dec c c') SB&
           (list_eq_dec Eqb_dec args args') SB&
           (sort_eq_dec t t')
         | sort_eq_rule c t1 t2, sort_eq_rule c' t1' t2' =>
           SB! (ctx_eq_dec c c') SB&
           (sort_eq_dec t1 t1') SB&
           (sort_eq_dec t2 t2')
         | term_eq_rule c e1 e2 t, term_eq_rule c' e1' e2' t' =>
           SB! (ctx_eq_dec c c') SB&
           (term_eq_dec e1 e1') SB&
           (term_eq_dec e2 e2') SB&
           (sort_eq_dec t t')
         | _,_ => _
         end); basic_term_crush.
Defined.

Definition compute_incl_lang (l1 l2 : lang) :=
  if incl_dec (pair_eq_dec Eqb_dec rule_eq_dec) l1 l2 then true else false.

Lemma use_compute_incl_lang (l1 l2 : lang)
  : compute_incl_lang l1 l2 = true -> incl l1 l2.
Proof.
  unfold compute_incl_lang.
  destruct (incl_dec _ l1 l2); easy.
Qed.


End WithVar.
#[export] Hint Constructors rule : term.
#[export] Hint Rewrite invert_eq_sort_rule_sort_rule : term.
#[export] Hint Rewrite invert_eq_sort_rule_term_rule : term.
#[export] Hint Rewrite invert_eq_sort_rule_sort_eq_rule : term.
#[export] Hint Rewrite invert_eq_sort_rule_term_eq_rule : term.
#[export] Hint Rewrite invert_eq_term_rule_sort_rule : term.
#[export] Hint Rewrite invert_eq_term_rule_term_rule : term.
#[export] Hint Rewrite invert_eq_term_rule_sort_eq_rule : term.
#[export] Hint Rewrite invert_eq_term_rule_term_eq_rule : term.
#[export] Hint Rewrite invert_eq_sort_eq_rule_sort_rule : term.
#[export] Hint Rewrite invert_eq_sort_eq_rule_term_rule : term.
#[export] Hint Rewrite invert_eq_sort_eq_rule_sort_eq_rule : term.
#[export] Hint Rewrite invert_eq_sort_eq_rule_term_eq_rule : term.
#[export] Hint Rewrite invert_eq_term_eq_rule_sort_rule : term.
#[export] Hint Rewrite invert_eq_term_eq_rule_term_rule : term.
#[export] Hint Rewrite invert_eq_term_eq_rule_sort_eq_rule : term.
#[export] Hint Rewrite invert_eq_term_eq_rule_term_eq_rule : term.
#[export] Hint Resolve reconstruct_ws_lang : term.
#[export] Hint Resolve ws_lang_all_ws_rule : term.


(*Moved out of the module because Coq seems
  to include them at the the top level anyway
 *)
Declare Custom Entry constr_arg_list.

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
  
  Declare Scope lang_scope.
  Bind Scope lang_scope with lang.

  Declare Scope rule_scope.
  Delimit Scope rule_scope with rule.

  Notation "{[l r1 ; .. ; r2 ]}" :=
    ((cons r2 .. (cons r1 nil) ..))%rule
      (format "'[' {[l '[hv' r1 ; '/' .. ; '/' r2 ']' ]} ']'") : lang_scope.
  
  Notation "e .. e'" :=
    (cons e' .. (cons e nil) ..)%string
    (in custom constr_arg_list at level 50,
        e constr at level 0, e' constr at level 0,
        format " '[hv' e  ..  e' ']'").

  Notation "" :=
    nil
      (in custom constr_arg_list at level 0).


Notation "'[s|' G ----------------------------------------------- # s args 'srt' ]" :=
  (s, sort_rule G args)
    (s constr at level 0,
     args custom constr_arg_list at level 100,
     G custom ctx at level 100,
     format "'[' [s|  '[' G '//' ----------------------------------------------- '//' '[' # s args  'srt' ']' ']' '//' ] ']'")
  : rule_scope.

Check [s| "x" : #"env", "y" : #"ty" "x", "z" : #"ty" "x"
          -----------------------------------------------
          #"foo" "y" "z" srt                             ]%rule.

Check [s| 
          -----------------------------------------------
            #"env" srt                                   ]%rule.

          
Notation "[:| G ----------------------------------------------- # s args : t ]" :=
  (s, term_rule G args t)
    (s constr at level 0,
     args custom constr_arg_list at level 100,
     G custom ctx at level 100, t custom sort at level 100,
     format "'[' [:|  '[' G '//' ----------------------------------------------- '//' '[' # s args  '/' :  t ']' ']' '//' ] ']'") : rule_scope.

Check [:| "G" : #"env",
          "A" : #"ty" "G",
          "B" : #"ty" "x",
          "e" : #"el" (#"wkn" "A" "B")
          -----------------------------------------------
          #"lam" "A" "e" : #"el" (#"->" "A" "B")         ]%rule.


Check [:|
          -----------------------------------------------
                      #"emp" : #"env"                     ]%rule.

Eval compute in
     [:|
          -----------------------------------------------
                      #"emp" : #"env"                    ]%rule.

Check [:| "G" : #"env",
           "A" : #"ty" "G",
           "B" : #"ty" "x",
           "e" : #"el" (#"wkn" "A" "B")
           -----------------------------------------------
           #"lam" "e" : #"el" (#"->" "A" "B")             ]%rule.

Notation "'[s=' G ----------------------------------------------- ( s ) e1 = e2 ]" :=
  (s%string, sort_eq_rule G e1 e2)
    (s constr at level 0, G custom ctx at level 100,
     e1 custom sort at level 100, e2 custom sort at level 100,
     format "'[' [s=  '[' G '//' -----------------------------------------------  ( s ) '//' '[' e1 '/'  =  e2 ']' ']' '//' ] ']'")
  : rule_scope.


Check [s= "G" : #"env", "A" : #"ty" "G", "B" : #"ty" "G",
          "eq" : #"ty_eq" "G" "A" "B" 
          ----------------------------------------------- ("ty_eq_sort")
          #"ty" "G" "A" = #"ty" "G" "B"
      ]%rule.
           
Notation "[:= G ----------------------------------------------- ( s ) e1 = e2 : t ]" :=
  (s%string, term_eq_rule G e1 e2 t)
    (s constr at level 0, G custom ctx at level 100,
     t custom sort at level 100,
     e1 custom term at level 100, e2 custom term at level 100, 
     format "'[' [:=  '[' G '//' -----------------------------------------------  ( s ) '//' '[' e1 '/'  =  e2 ']' '/'  :  t ']' '//' ] ']'")
  : rule_scope.


Check [:= "G" : #"env", "A" : #"ty" "G", "B" : #"ty" "G",
          "eq" : #"ty_eq" "G" "A" "B" 
          ----------------------------------------------- ("ty_eq_sort")
          "A" = "B" : #"ty" "G"
      ]%rule.

End Notations.
