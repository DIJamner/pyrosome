Set Implicit Arguments.

Require Import Lists.List Datatypes.String Bool.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Substable Term Rule.
From Pyrosome.Elab Require Import PreTerm.
Import PreTerm.Notations.


Section WithVar.
  Context (V : Type).

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  
  Notation preterm := (@preterm V).
  Notation prectx := (@prectx V).
  Notation presort := (@presort V).
  
  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).

Inductive prerule :=
| presort_rule : prectx -> list V (*explicit args*) -> prerule
| preterm_rule : prectx -> list V (*explicit args*) -> presort -> prerule
| presort_eq_rule : prectx -> presort -> presort -> prerule
| preterm_eq_rule : prectx -> preterm -> preterm -> presort -> prerule.

Instance default_prerule : WithDefault prerule := presort_rule [] [].

Definition prelang := named_list prerule.


Definition of_rule r :=
  match r with
  | sort_rule x x0 => presort_rule (of_ctx x) x0
  | term_rule x x0 x1 => preterm_rule (of_ctx x) x0 (of_sort x1)
  | sort_eq_rule x x0 x1 => presort_eq_rule (of_ctx x) (of_sort x0) (of_sort x1)
  | term_eq_rule x x0 x1 x2 =>
      preterm_eq_rule (of_ctx x) (of_term x0) (of_term x1) (of_sort x2) 
  end.

Definition to_rule r :=
  match r with
  | presort_rule x x0 => sort_rule (to_ctx x) x0
  | preterm_rule x x0 x1 => term_rule (to_ctx x) x0 (to_sort x1)
  | presort_eq_rule x x0 x1 => sort_eq_rule (to_ctx x) (to_sort x0) (to_sort x1)
  | preterm_eq_rule x x0 x1 x2 =>
      term_eq_rule (to_ctx x) (to_term x0) (to_term x1) (to_sort x2) 
  end.

Definition of_lang := named_map of_rule.
Definition to_lang := named_map to_rule.

(*
Context
  {V_Eqb : Eqb V}
    {V_default : WithDefault V}.

 TODO: implement eqb for preterm, presort
#[export] Instance prerule_eqb : Eqb prerule :=
  fun r1 r2 =>
    match r1, r2 with
    | presort_rule c args, presort_rule c' args' =>
        (eqb c c') && (eqb args args')
    | preterm_rule c args t, preterm_rule c' args' t' =>
        (eqb c c') &&
          (eqb args args') &&
          (eqb t t')
    | presort_eq_rule c t1 t2, presort_eq_rule c' t1' t2' =>
        (eqb c c') &&
          (eqb t1 t1') &&
          (eqb t2 t2')
    | preterm_eq_rule c e1 e2 t, preterm_eq_rule c' e1' e2' t' =>
        (eqb c c') &&
          (eqb e1 e1') &&
          (eqb e2 e2') &&
          (eqb t t')
    | _,_ => false
    end. *)

End WithVar.

(*Moved out of the module because Coq seems
  to include them at the the top level anyway
 *)
Declare Custom Entry pre_constr_arg_list.

Declare Custom Entry prerule_body.

Module Notations.

  Export PreTerm.Notations.
  
  Declare Scope prelang_scope.
  Bind Scope prelang_scope with prelang.

  Declare Scope prerule_scope.
  Delimit Scope prerule_scope with prerule.

  Notation "{[l r1 ; .. ; r2 ]}" :=
    ((cons r2 .. (cons r1 nil) ..))%prerule
      (format "'[' {[l '[hv' r1 ; '/' .. ; '/' r2 ']' ]} ']'") : prelang_scope.

  
  
  Notation "e .. e'" :=
    (cons e' .. (cons e nil) ..)%string
    (in custom pre_constr_arg_list at level 50,
        e constr at level 0, e' constr at level 0,
        format " '[hv' e  ..  e' ']'").

  Notation "" :=
    nil
      (in custom pre_constr_arg_list at level 0).

  
Notation "'{[r' G ----------------------------------------------- rb ]}" :=
  (fst rb , snd rb G)
    (rb custom prerule_body at level 100,
     G custom pre_ctx at level 100)
    : prerule_scope.

(* TODO: hardcode string here or no? *)
Notation "# s args 'srt'" :=
  (s, fun G : prectx string => presort_rule G args)
    (in custom prerule_body,
        s constr at level 0,
     args custom pre_constr_arg_list at level 100)
  : prerule_scope.

(* Use this pattern instead of `Check` to avoid polluting the output of `make` *)
Goal let x :=
       {[r "x" : #"env", "y" : #"ty" "x", "z" : #"ty" "x"
          -----------------------------------------------
          #"foo" "y" "z" srt                             ]}%prerule
     in False.
Abort.


(*TODO: why does this not work with the scope?*)
Notation "" := nil (*(@nil (string*sort))*) (in custom pre_ctx at level 0).

Goal let x : _* prerule string :=
       {[r 
          -----------------------------------------------
            #"env" srt                                   ]}%prerule
     in False.
Abort.

          
Notation "# s args : t" :=
  (s, fun G : prectx string => preterm_rule G args t)
    (in custom prerule_body,
        s constr at level 0,
        t custom presort at level 100,
     args custom pre_constr_arg_list at level 100) : prerule_scope.

Goal let x :=
       {[r "G" : #"env",
          "A" : #"ty" "G",
          "B" : #"ty" "x",
          "e" : #"el" (#"wkn" "A" "B")
          -----------------------------------------------
          #"lam" "A" "e" : #"el" (#"->" "A" "B")         ]}%prerule
     in False.
Abort.


Goal let x :=
       {[r
          -----------------------------------------------
                      #"emp" : #"env"                     ]}%prerule
     in False.
Abort.


Goal let x :=
        {[r "G" : #"env",
           "A" : #"ty" "G",
           "B" : #"ty" "x",
           "e" : #"el" (#"wkn" "A" "B")
           -----------------------------------------------
           #"lam" "e" : #"el" (#"->" "A" "B")             ]}%prerule
     in False.
Abort.

Notation "( s ) e1 = e2 'srt'" :=
  (s%string, fun G : prectx string => presort_eq_rule G e1 e2)
    (in custom prerule_body at level 100,
        s constr at level 0,
     e1 custom presort at level 100, e2 custom presort at level 100)
  : prerule_scope.

Goal let x :=
        {[r "G" : #"env", "A" : #"ty" "G", "B" : #"ty" "G",
          "eq" : #"ty_eq" "G" "A" "B" 
          ----------------------------------------------- ("ty_eq_sort")
          #"ty" "G" "A" = #"ty" "G" "B" srt
        ]}%prerule
     in False.
Abort.
           
Notation "( s ) e1 = e2 : t" :=
  (s%string,fun G : prectx string => preterm_eq_rule G e1 e2 t)
    (in custom prerule_body at level 100,
     s constr at level 0,
     t custom presort at level 100,
     e1 custom preterm at level 100, e2 custom preterm at level 100)
  : prerule_scope.



Goal let x :=
        {[r "G" : #"env", "A" : #"ty" "G", "B" : #"ty" "G",
          "eq" : #"ty_eq" "G" "A" "B" 
          ----------------------------------------------- ("ty_eq_sort")
          "A" = "B" : #"ty" "G"
        ]}%prerule
     in False.
Abort.

End Notations.
