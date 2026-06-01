Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import
  Domain Apply Reflect Typing Preservation LogRel.
Import Core.Notations.

Notation term := (@term string).

(* ===================================================================== *)
(* Closure lemmas for the reducibility relation (Milestone 1).             *)
(*                                                                         *)
(* ESCAPE (this file, all Qed): reducibility implies well-formedness.       *)
(* The harder closure lemmas [reflect_red] (totality of [Reflect]) and      *)
(* [Apply_total_red] (totality of [Apply_*] on reducible inputs), together  *)
(* with [RedTy_subst]/[RedSub_*], need a CUSTOM nested induction principle  *)
(* for [LR] that supplies induction hypotheses for the [PolyRedPackAdequate] *)
(* sub-derivations (Coq's auto-generated [LR_rect] does not recurse into     *)
(* the adequacy record).  Deriving that principle (cf. logrel-coq's          *)
(* [Induction.v]) is the next infrastructure step; the escape lemmas below   *)
(* need no induction hypotheses and are independent of it.                   *)
(* ===================================================================== *)

(* A reducible type is well-formed.  Each case is immediate: base codes are
   typed by [t_Nat]/[t_Empty]/[t_ne], the Pi case returns the stored escape
   fact, and the universe is [wf_dU]. *)
Lemma RedTy_wf : forall Ge T, RedTy Ge T -> wf_svalty Ge T.
Proof.
  intros Ge T [P HLR]. unfold LR2 in HLR. destruct HLR.
  - apply (wf_dEl (r := con "rel" []) (l := con "L0" [])). apply t_Nat.
  - apply (wf_dEl (r := con "irr" []) (l := con "L0" [])). apply t_Empty.
  - eapply wf_dEl. apply t_ne. eassumption.
  - assumption.
  - assumption.
  - apply wf_dU.
Qed.

(* A reducible term is well-typed at its type. *)
Lemma RedTm_wf : forall Ge T v, RedTm Ge T v -> has_svalty Ge v T.
Proof.
  intros Ge T v [P [HLR Pv]]. unfold LR2 in HLR. destruct HLR.
  - (* Nat : induction on the reducible-natural witness *)
    induction Pv.
    + apply t_zero.
    + apply t_suc; assumption.
    + apply t_ne; assumption.
  - (* Empty *) destruct Pv as [m wm]. apply t_ne; exact wm.
  - (* neutral El *) destruct Pv as [m wm]. apply t_ne; exact wm.
  - (* PiI : the predicate is exactly the typing *) exact Pv.
  - (* Pi : first component of [PiRedTmPred] is the typing *) exact (fst Pv).
  - (* Universe : first component is the typing *) exact (fst Pv).
Qed.
