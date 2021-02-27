Require Import mathcomp.ssreflect.all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


From Ltac2 Require Import Ltac2.
From Utils Require Import Utils.
From Named Require Import Pf PfCore.
Require Import String PfMatches.


Set Default Proof Mode "Ltac2".

Import OptionMonad.



(*If the LHS a rule directly applies to e, return the proof.
  Rules are scanned from the root of the language.
  Works for both terms and sorts
 *)

Section StepWithPat.
  Context (c : pf_ctx)
          (pat_in : pf)
          (name : string).

  Definition step_redex (e : pf) : option pf :=
  do s <- matches e pat_in (map fst c);
     ret (ax name s).

  Section InnerLoop.
    Context (step_pat : forall (e : pf), option pf).
    Fixpoint args_step s : option (list pf) :=
      match s with
      | [::] => None
      | e::s' =>
        match args_step s' with
        | Some s'' => Some (e::s'')
        | None =>
          do e' <- step_pat e;
             ret (e'::s')
        end
      end.
  End InnerLoop.

  Fixpoint step_pat (e : pf) : option pf :=
    match step_redex e, e with
    | Some e',_ => Some e'
    | None, pvar _ => None
    | None, pcon name s =>
      do s' <- args_step step_pat s;
      ret (pcon name s')
    | None, _ => None
    end.
End StepWithPat.

(*TODO: can optimize sort rule step to not be recursive *)
Definition rule_step_left l n e : option pf :=
  match named_list_lookup_err l n with
  | Some (term_le_pf c e1 _ _)
  | Some (sort_le_pf c e1 _) =>
    step_pat c e1 n e
  | _ => None
  end.

Definition rule_step_right l n e : option pf :=
  match named_list_lookup_err l n with
  | Some (term_le_pf c _ e2 _)
  | Some (sort_le_pf c _ e2) =>
    step_pat c e2 n e
  | _ => None
  end.
