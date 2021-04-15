Set Implicit Arguments.
Set Bullet Behavior "Strict Subproofs".

Require Import String List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Named Require Import Core Matches.
Import Core.Notations.
Import OptionMonad.


(*
(* 0 or more parallel steps (involving disjoint parts of the AST) *)
Inductive term_steps_par (l : lang) : pf -> sort -> exp -> exp -> Prop :=
  | term_redex_steps_par : forall name c' e1' e2' t' s,
      (name, term_le c' e1' e2' t') \in l ->
      map fst s = map fst c' ->
      term_steps_par (ax name s) l t'[/s/] e1'[/s/] e2'[/s/]
  | term_eval_ctx_steps_par : forall ename c' t' args1 args2 args s1 s2,
      args_steps_par pfl l c' args1 args2 args s1 s2 ->
      term_steps_par (pcon ename pfl) l t'[/with_names_from c' s2/] (con ename args1) (con ename args2)
with args_steps_par (l:lang) : list pf -> ctx ->
                               list exp -> list exp ->
                               list string -> list exp -> list exp -> Prop :=
  | args_steps_par_nil : args_steps_par [::] l [::] [::] [::] [::] [::] [::]
  (* TODO: have an implicit one? prob not necessary *)
  | fst_arg_steps_par : forall ename e1 e2 t args args1' args2' s1 s2 c',
      term_steps_par l t[/with_names_from c' s2 /] e1 e2 ->
      args_steps_par l c' args1' args2' args s1 s2 ->
      args_steps_par l ((ename,t)::c') (e1::args1') (e2::args2') (ename::args) (e1::s1) (e2::s2)
  | rst_arg_steps_par_ex : forall ename e t args1' args2' c' args s1 s2,
      args_steps_par l c' args1' args2' args s1 s2 ->
      args_steps_par l ((ename,t)::c') (e::args1') (e::args2') (ename::args) (e::s1) (e::s2)
  | rst_arg_steps_par_im : forall ename e t args1' args2' c' args s1 s2,
      args_steps_par l c' args1' args2' args s1 s2 ->
      args_steps_par l ((ename,t)::c') (args1') (args2') (args) (e::s1) (e::s2).
*)

(*If the LHS of a term eq rule directly applies to e, return the proof.
  Rules are scanned from the root of the language.
  Works for both terms and sorts
 *)
Fixpoint step_redex_term (l : lang) (e : exp) : option (exists c t e', eq_term l c t e e').
  refine (match l with
          | [] => None
          | (n,term_eq_rule c e1 e2 t)::l' =>
            match step_redex_term l' e with
            | Some t' => Some _
            | None => do s <- matches e e1 (map fst c);
                         ret (ax n s)
            end
         | _::l' => step_redex l' e
         end).


(* TODO: define as option or iterate to a fixed point? *)
Section InnerLoop.
  Context (par_step : forall (l : pf_lang) (e : pf), option pf).
  Fixpoint args_par_step l s {struct s} : option (list pf) :=
    match s with
    | [::] => None
    | e::s' =>
      match par_step l e, args_par_step l s' with
      | Some e', Some s'' => Some (e'::s'')
      | Some e', None => Some (e'::s')
      | None, Some s'' => Some (e::s'')
      | None, None => None
      end
    end.
End InnerLoop.

(*Note only returns results on pfs satisfying is_exp *)
Fixpoint par_step (l : pf_lang) (e : pf) {struct e} : option pf :=
  match step_redex l e, e with
  | Some e',_ => Some e'
  | None, pvar _ => None
  | None, pcon name s =>
    do s' <- args_par_step par_step l s;
    ret (pcon name s')
  | None, _ => None
  end.

(* Generates a proof of reduction for as many steps as possible,
   up to 'fuel'.
 *)
Fixpoint par_step_n (l : pf_lang) (e : pf) (fuel : nat) : pf :=
  match fuel, par_step l e with
  | 0,_ => e
  | S _, None => e
  | S fuel', Some e' =>
    trans e' (par_step_n l (proj_r l e') fuel')
  end.
