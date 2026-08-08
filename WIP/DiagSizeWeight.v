(* Experiment: does a genuine SIZE weight (oP_add over children) change
   extraction, and does it stop the goal-2 blowup? *)
From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List BinNums BinPos.
Import ListNotations. Open Scope string. Open Scope list.
From Utils Require Import Utils EGraph.Defs.
From Pyrosome Require Import Theory.Core Compilers.Compilers
  Elab.Elab Elab.ElabCompilers Tools.Matches Tools.EGraph.Automation
  Tools.EGraph.TypeInference Tools.EGraph.ComputeWf Tools.Resolution
  Tools.EGraph.Defs.
From Pyrosome.Lang Require Import
  PolySubst SimpleVSubst SimpleVSTLC SimpleVCPS SimpleVFix SimpleVFixCPS.
Import Core.Notations.
Import CompilerDefs.Notations.

Definition oadd (a b : option positive) : option positive :=
  match a, b with Some x, Some y => Some (x + y)%positive | _, _ => None end.
Definition omin (a b : option positive) : option positive :=
  match a, b with None,_ => b | _,None => a | Some x, Some y => Some (Pos.min x y) end.

(* SIZE analysis: combine children with oadd (sum), not max. *)
#[local] Instance size_an : analysis string string (option positive) :=
  {| analyze a arg_as :=
       match arg_as with
       | [] => Some 1%positive
       | a0 :: r => oadd (Some 1%positive) (fold_left oadd r a0)
       end;
     analysis_meet := omin |}.

Fixpoint tsize (e : Term.term string) : nat :=
  match e with var _ => 1 | con _ args => S (fold_right (fun a n => tsize a + n) 0 args) end.
Fixpoint tdepth (e : Term.term string) : nat :=
  match e with var _ => 1 | con _ args => S (fold_right (fun a n => Nat.max (tdepth a) n) 0 args) end.

Ltac size_probe :=
  lazymatch goal with
  | |- eq_term ?l ?c ?t ?e1 ?e2 =>
    let nf1 := constr:(@PositiveInstantiation.egraph_simpl' string _ _ (option positive)
                 size_an l 100 30 100 c e1) in
    let s_in  := eval vm_compute in (tsize e1) in
    let s_out := eval vm_compute in (tsize nf1) in
    let d_out := eval vm_compute in (tdepth nf1) in
    idtac "SIZE-weight: input size" s_in " -> extract size" s_out " depth" d_out
  | |- ?g => idtac "(skip)"
  end.

Goal (elab_preserving_compiler (cps++cps_subst)
        (fix_cps_lang ++ cps_prod_lang ++ cps_lang ++ block_subst ++ value_subst)
        fix_cps_def fix_cps fix_lang).
Proof. idtac "===== SIZE-WEIGHT extraction ====="; cleanup_elab_after setup_elab_compiler;
  [> repeat Matches.t .. ]; try decompose_sort_eq; size_probe. Abort.
