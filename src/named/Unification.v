Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Require Import String.
From Utils Require Import Utils Monad.
From Named Require Import Exp Rule Core.

(* Elaboration recognizers are more tricky than
   wfness ones because elaboration requires
   generation of implicit proof terms.

   TODO: come up with a good way to do it; ideas below:
*)
Require IExp IRule ICore.
Require Import ARule.
Require Import UExp.
Require Import ZArith.

Record uvar_data := mkuvar {
  uvar_name: string (* for humans*);
  uvar_ident: N;
  uvar_subst : subst}.

Definition uvar_from_data (d : uvar_data) : exp :=
  let (n,i,s):= d in uvar n i s.


Definition suvar_from_data (d : uvar_data) : sort :=
  let (n,i,s):= d in suvar n i s.

Variant unif_clause :=
| unif_wf_term (c:ctx)  (x : uvar_data) (t:sort)
| unif_le_term (c:ctx) (e1 e2 : exp) (t:sort)
| unif_wf_sort (c:ctx) (x:uvar_data)
| unif_le_sort (c:ctx) (t1 t2 : sort).

Definition with_unification (A : Set) : Set :=
  N -> list unif_clause -> option (A * list unif_clause * N).

Definition add_clauses uc' : with_unification unit :=
  fun n uc => Some (tt, uc'++uc,n).

Definition add_clause uc' : with_unification unit :=
  fun n uc => Some (tt, uc'::uc, n).


Instance unification_monad : Monad with_unification :=
  {
  Mret _ e := fun n uc => Some (e,uc,n);
  Mbind _ _ f me n uc :=
    match me n uc with
    | Some (e, ucs,n') => (f e n' ucs)
    | None => None
    end;
  Mfail _ := fun _ _ => None
  }.

Definition lookup_rule l n : with_unification rule :=
  match named_list_lookup_err l n with
  | Some r => fun n uc => Some (r,uc,n)
  | None => fun _ _ => None
  end.


Definition newvar_with_subst (x : string) s : with_unification uvar_data :=
  fun n uc => Some ((mkuvar x n s), uc,(n+1)%N).

Definition newvar (x : string) (args : list string) : with_unification uvar_data :=
  newvar_with_subst x (map (fun y => (y, var y)) args).


Fixpoint exp_from_core (e : Exp.exp) : exp :=
  match e with
  | Exp.var x => var x
  | Exp.con n s => con n (map exp_from_core s)
  end.

Definition sort_from_core t : sort :=
  match t with
  | Exp.scon n s => scon n (map exp_from_core s)
  end.

Definition ctx_from_core : Exp.ctx -> ctx := named_map sort_from_core.
    
Fixpoint elab_args_unif_fuel l c args s c' (fuel:nat) {struct fuel} : with_unification (list exp) :=
  match c',args, s, fuel with
  | [::],[::],[::],_ => do ret [::]
  | (n,t)::c'',[::],[::],fuel'.+1 =>
    do es <- elab_args_unif_fuel l c args s c'' fuel';
       n_fr <- newvar n (map fst c);
       tt <- add_clause (unif_wf_term c n_fr (t:sort)[/with_names_from c'' es/]);
       ret ((uvar_from_data n_fr)::es)
  | (n,t)::c'', a::args',e::s', fuel'.+1 =>
    if n == a
    then do es <- elab_args_unif_fuel l c args' s' c'' fuel';
            ee <- elab_term_unif_fuel l c e t[/with_names_from c'' es/] fuel';
            ret (ee::es)
    else 
    do es <- elab_args_unif_fuel l c args s c'' fuel';
       n_fr <- newvar n (map fst c);
       tt <- add_clause (unif_wf_term c n_fr (t:sort)[/with_names_from c'' es/]);
       ret ((uvar_from_data n_fr)::es)
  | _, _,_,_ => Mfail
end
with elab_term_unif_fuel (l:lang) c (e:IExp.exp) t (fuel : nat) : with_unification exp :=
       match e, fuel with
       | IExp.var x, _ => do ret (var x)
       | IExp.con n s, fuel'.+1 =>
         do (term_rule c' args t') <?- lookup_rule l n;
            es <- elab_args_unif_fuel l c args s (ctx_from_core c') fuel';
            tt <- let t'' := (sort_from_core t')[/with_names_from c' es/] in
                  add_clause (unif_le_sort c t t'');
            ret (con n es)
       | _, _ => Mfail (*TODO: ann?*)
         end.

Definition elab_args_unif l c args s c' :=
  elab_args_unif_fuel l c args s c' 0. (* TODO: how much fuel is enough?*)

Definition elab_term_unif l c e t :=
  elab_term_unif_fuel l c e t 0.  (* TODO: how much fuel is enough?*)
                                           

Definition elab_sort_unif (l : lang) (c : ctx) (t : IExp.sort)
  : with_unification sort :=
  match t with
  | IExp.scon n s =>
    do (sort_rule c' args) <?- lookup_rule l n;
       es <- elab_args_unif l c args s (ctx_from_core c');
       ret (scon n es)
end.

Record answer :Set := {
  fill_uvar :N -> exp;
  fill_suvar : N-> sort;
}.

Inductive satisfying_answer (l : (a : answer) : list unif_clause -> Prop :=
| satisfying_nil : satisfying_answer a [::]
| satisfying_wf_sort : forall,
    satisfying_answer a l ->
    satisfying_answer a (unif_wf_sort.

