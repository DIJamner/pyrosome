Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import List String Bool.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Substable Term.
(*TODO: why does this generate warnings?*)
Import Term.Notations.
Import SumboolNotations.


Section WithVar.
  Context (V : Type).

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
Proof using. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_sort_rule_sort_rule : term.

Lemma invert_eq_sort_rule_term_rule c c' args args' t'
  : sort_rule c args = term_rule c' args' t' <-> False.
Proof using. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_sort_rule_term_rule : term.


Lemma invert_eq_sort_rule_sort_eq_rule c c' args t1' t2'
  : sort_rule c args = sort_eq_rule c' t1' t2' <-> False.
Proof using. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_sort_rule_sort_eq_rule : term.

Lemma invert_eq_sort_rule_term_eq_rule c c' args e1' e2' t
  : sort_rule c args = term_eq_rule c' e1' e2' t <-> False.
Proof using. solve_invert_constr_eq_lemma. Qed.
Hint Rewrite invert_eq_sort_rule_term_eq_rule : term.
  
Lemma invert_eq_term_rule_sort_rule c c' args args' t
  : term_rule c args t = sort_rule c' args' <-> False.
Proof using. solve_invert_constr_eq_lemma. Qed.
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

Context
  {V_Eqb : Eqb V}
    {V_default : WithDefault V}.

Notation well_scoped := (well_scoped (V:=V) (A:=term)).
  
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


Lemma ws_lang_nil_inv
  : ws_lang [] <-> True.
Proof.
  cbv [ws_lang]; basic_goal_prep;
  basic_term_crush.
Qed.

Lemma ws_lang_cons_inv n r (l : lang)
  : ws_lang ((n, r) :: l)
    <-> fresh n l /\ ws_rule r /\ ws_lang l.
Proof.
  cbv [ws_lang]; basic_goal_prep;
  basic_term_crush.
Qed.

Lemma rule_in_ws (l : lang) n r : ws_lang l -> In (n,r) l -> ws_rule r.
Proof using .
  induction l; 
    basic_goal_prep;
    basic_term_firstorder_crush.
Qed.

Lemma reconstruct_ws_lang (l : lang)
  : all_fresh l /\ all ws_rule (map snd l) -> ws_lang l.
Proof.
  eauto.
Qed.
Hint Resolve reconstruct_ws_lang : term.

Lemma ws_lang_all_ws_rule (l : lang)
  : ws_lang l -> all ws_rule (map snd l).
Proof.
  unfold ws_lang; intuition.
Qed.
Hint Resolve ws_lang_all_ws_rule : term.

#[export] Instance rule_eqb : Eqb rule :=
  fun r1 r2 =>
    match r1, r2 with
    | sort_rule c args, sort_rule c' args' =>
        (eqb c c') && (eqb args args')
    | term_rule c args t, term_rule c' args' t' =>
        (eqb c c') &&
          (eqb args args') &&
          (eqb t t')
    | sort_eq_rule c t1 t2, sort_eq_rule c' t1' t2' =>
        (eqb c c') &&
          (eqb t1 t1') &&
          (eqb t2 t2')
    | term_eq_rule c e1 e2 t, term_eq_rule c' e1' e2' t' =>
        (eqb c c') &&
          (eqb e1 e1') &&
          (eqb e2 e2') &&
          (eqb t t')
    | _,_ => false
    end.

Context {Eqb_V_ok : Eqb_ok V_Eqb}.

#[export] Instance rule_eqb_ok : Eqb_ok rule_eqb.
Proof.
  intros a b.
  unfold eqb.
  unfold rule_eqb.
  destruct a;
    destruct b;
    try case_match;
    basic_term_crush.
Qed.

Definition get_ctx (r : rule) :=
  match r with
  | sort_rule c _
  | term_rule c _ _
  | sort_eq_rule c _ _
  | term_eq_rule c _ _ _ => c
  end.
  
    (*TODO: move to Utils?*)
    (* Note: does not error out on bad inputs *)
    Fixpoint select_sublist {A} (s : named_list A) (filter : list V) :=
      match s, filter with
      | [], _ | _, [] => []
      | (n,a)::s', n'::filter' =>
          if eqb n n' then a::(select_sublist s' filter')
          else (select_sublist s' filter)
      end.

  (* Converts an elaborated term/sort/etc to an unelaborated one.
     Used for more readable goals. *)
  Section HideImplicits.
    Context (l : lang).
    
    Fixpoint hide_term_implicits (e : Term.term V) :=
      match e with
      | var x => var x
      | con n s =>
          match named_list_lookup_err l n with
          | Some (term_rule c args _) =>
              con n (select_sublist (combine (map fst c) (map hide_term_implicits s)) args)
          | _ => default
          end
      end.

    Definition hide_sort_implicits t :=
      match t with
      | scon n s =>
          match named_list_lookup_err l n with
          | Some (sort_rule c args) =>
              scon n (select_sublist (combine (map fst c) (map hide_term_implicits s)) args)
          | _ => default
          end
      end.

    Definition hide_ctx_implicits : ctx -> ctx := named_map hide_sort_implicits.

    Definition hide_rule_implicits r :=
      match r with
      | sort_rule c args => sort_rule (hide_ctx_implicits c) args
      | term_rule c args t => term_rule (hide_ctx_implicits c) args (hide_sort_implicits t)
      | sort_eq_rule c t t'=>
          sort_eq_rule (hide_ctx_implicits c) (hide_sort_implicits t) (hide_sort_implicits t')
      | term_eq_rule c e e' t =>
          term_eq_rule (hide_ctx_implicits c)
                       (hide_term_implicits e)
                       (hide_term_implicits e')
                       (hide_sort_implicits t)
      end.

    (* TODO: doesn't work properly (input needs to be in base *)
    Definition hide_lang_implicits : lang -> lang := named_map hide_rule_implicits.

  End HideImplicits.

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
(* `using assumption` necessary to choose a V *)
#[export] Hint Rewrite ws_lang_nil_inv using assumption : term.
#[export] Hint Rewrite  ws_lang_cons_inv : term.
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

(* Use this pattern instead of `Check` to avoid polluting the output of `make` *)
Goal let x :=
       [s| "x" : #"env", "y" : #"ty" "x", "z" : #"ty" "x"
          -----------------------------------------------
          #"foo" "y" "z" srt                             ]%rule
     in False.
Abort.

Goal let x : _* rule string :=
       [s| 
          -----------------------------------------------
            #"env" srt                                   ]%rule
     in False.
Abort.

          
Notation "[:| G ----------------------------------------------- # s args : t ]" :=
  (s, term_rule G args t)
    (s constr at level 0,
     args custom constr_arg_list at level 100,
     G custom ctx at level 100, t custom sort at level 100,
     format "'[' [:|  '[' G '//' ----------------------------------------------- '//' '[' # s args  '/' :  t ']' ']' '//' ] ']'") : rule_scope.

Goal let x :=
       [:| "G" : #"env",
          "A" : #"ty" "G",
          "B" : #"ty" "x",
          "e" : #"el" (#"wkn" "A" "B")
          -----------------------------------------------
          #"lam" "A" "e" : #"el" (#"->" "A" "B")         ]%rule
     in False.
Abort.


Goal let x :=
       [:|
          -----------------------------------------------
                      #"emp" : #"env"                     ]%rule
     in False.
Abort.


Goal let x :=
        [:| "G" : #"env",
           "A" : #"ty" "G",
           "B" : #"ty" "x",
           "e" : #"el" (#"wkn" "A" "B")
           -----------------------------------------------
           #"lam" "e" : #"el" (#"->" "A" "B")             ]%rule
     in False.
Abort.

Notation "'[s=' G ----------------------------------------------- ( s ) e1 = e2 ]" :=
  (s%string, sort_eq_rule G e1 e2)
    (s constr at level 0, G custom ctx at level 100,
     e1 custom sort at level 100, e2 custom sort at level 100,
     format "'[' [s=  '[' G '//' -----------------------------------------------  ( s ) '//' '[' e1 '/'  =  e2 ']' ']' '//' ] ']'")
  : rule_scope.



Goal let x :=
        [s= "G" : #"env", "A" : #"ty" "G", "B" : #"ty" "G",
          "eq" : #"ty_eq" "G" "A" "B" 
          ----------------------------------------------- ("ty_eq_sort")
          #"ty" "G" "A" = #"ty" "G" "B"
        ]%rule
     in False.
Abort.
           
Notation "[:= G ----------------------------------------------- ( s ) e1 = e2 : t ]" :=
  (s%string, term_eq_rule G e1 e2 t)
    (s constr at level 0, G custom ctx at level 100,
     t custom sort at level 100,
     e1 custom term at level 100, e2 custom term at level 100, 
     format "'[' [:=  '[' G '//' -----------------------------------------------  ( s ) '//' '[' e1 '/'  =  e2 ']' '/'  :  t ']' '//' ] ']'")
  : rule_scope.



Goal let x :=
        [:= "G" : #"env", "A" : #"ty" "G", "B" : #"ty" "G",
          "eq" : #"ty_eq" "G" "A" "B" 
          ----------------------------------------------- ("ty_eq_sort")
          "A" = "B" : #"ty" "G"
        ]%rule
     in False.
Abort.

End Notations.
