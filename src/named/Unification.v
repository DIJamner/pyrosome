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

(*TODO: this is hacky, but easier to draft this way for now 
  TODO: sort vars still have to be done differently
*)
Definition cvar s := var (String Ascii.zero s).
Definition uvar s := var (String Ascii.Beep s).

Variant usort := uscon (n : string) (s: list exp) | usvar (x:string).

Variant unif_clause :=
| unif_wf_term (c:ctx) (x:string) (t:usort)
| unif_le_term (x:string) (e : exp)
| unif_wf_sort (c:ctx) (x:string)
| unif_le_sort (x : string) (t : usort).

Definition with_unification (A : Set) : Set :=
  option (A * list unif_clause).

Definition add_clauses uc : with_unification unit :=
  Some (tt, uc).

Definition add_clause uc : with_unification unit :=
  Some (tt, [::uc]).

(*TODO: this may not be quite right for wf term, wf sort; 
 wf_term should be inductive, return non-unit*)
Parameter add_unif_wf_term : ctx -> string -> usort -> with_unification unit.
Parameter add_unif_wf_sort : ctx -> string -> with_unification unit.
Parameter add_unif_le_term : ctx -> exp -> exp -> usort -> with_unification unit.
Parameter add_unif_le_sort : ctx -> usort -> usort -> with_unification unit.

Instance unification_monad : Monad with_unification :=
  {
  Mret _ e := Some (e,[::]);
  Mbind _ _ f me :=
    match me with
    | Some (e, ucs) =>
      Option.map (fun p:(_*_) => let (e,l):= p in (e,ucs++l)) (f e)
    | None => None
    end;
  Mfail _ := None
  }.

Definition lookup_rule l n : with_unification rule :=
  match named_list_lookup_err l n with
  | Some r => Some (r,[::])
  | None => None
  end.

Parameter elab_args_unif
  : lang -> ctx -> list string -> list exp -> ctx -> with_unification (list exp).

Definition elab_sort_unif (l : lang) (c : ctx) (t : sort)
  : with_unification usort :=
  match t with
  | srt n s =>
    (do (sort_rule c' args) <?- lookup_rule l n;
       es <- elab_args_unif l c args s c';
       ret (srt n es))
end.
