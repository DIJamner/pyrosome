Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
From Pyrosome.Gluing Require Import CutTModel Eval CutModelSound.
Require Import Pyrosome.Gluing.Dtt.Syntax Pyrosome.Gluing.Dtt.NormalForms Pyrosome.Gluing.Dtt.LogRel Pyrosome.Gluing.Dtt.RSub Pyrosome.Gluing.Dtt.Ceq
  Pyrosome.Gluing.Dtt.ModelStruct Pyrosome.Gluing.Dtt.ModelIdx Pyrosome.Gluing.Dtt.ModelBase Pyrosome.Gluing.Dtt.ModelSubst
  Pyrosome.Gluing.Dtt.ModelPi Pyrosome.Gluing.Dtt.ModelProofIrr.
Import Core.Notations.

(* =====================================================================
   LAYER 4b, ASSEMBLED.

   The 65 rule obligations were proved in five fragments, each with a
   dispatcher in the right field shape but restricted to its own rule
   names:

     src/Pyrosome/Gluing/Dtt/ModelIdx.v      the index formers          9 cong,  3 eq
     src/Pyrosome/Gluing/Dtt/ModelBase.v     universe and base types    6 cong,  6 eq
     src/Pyrosome/Gluing/Dtt/ModelSubst.v    the substitution calculus 10 cong, 13 eq
     src/Pyrosome/Gluing/Dtt/ModelPi.v       the binders                7 cong, 10 eq
     src/Pyrosome/Gluing/Dtt/ModelProofIrr.v proof irrelevance          0 cong,  1 eq
                                                    ---------------
                                                     32 cong, 33 eq

   This file checks that those name restrictions PARTITION the language --
   every one of [ott_dtt]'s 32 term rules and 33 equations is claimed by
   exactly one fragment -- and assembles [CongObligation] and
   [ByObligation].  With those, [DttCM_ok] is unconditional and so is
   normalization.
   ===================================================================== *)

(* [pin_name] (src/Pyrosome/Gluing/Dtt/ModelStruct.v) enumerates the
   language's 74 NAMES -- a disjunction of string literals, not of rules --
   so each case has a concrete name and can name its own fragment; the
   wrong fragments fail on the name disjunct rather than silently
   succeeding.  The names whose rule is of the OTHER kind (an equation
   here, a term rule there) are refuted by [pin_lookup], which computes
   that one rule and discriminates.

   Doing this by [vm_compute]ing the [In] premise instead put all 73
   fully-evaluated rules in the proof term, twice: 14.7 s for this file
   against 5.1 s. *)
Theorem cong_obligation : CongObligation.
Proof.
  intros c' name args t s1 s2 Hin Hargs.
  pin_name Hin.
  all: first
    [ eapply idx_cong_obligation;   [ exact Hin | tauto | exact Hargs ]
    | eapply base_cong_obligation;  [ exact Hin | tauto | exact Hargs ]
    | eapply subst_cong_obligation; [ exact Hin | tauto | exact Hargs ]
    | eapply pi_cong_obligation;    [ exact Hin | tauto | exact Hargs ]
    | pin_lookup ].
Qed.

Theorem by_obligation : ByObligation.
Proof.
  intros c' name e1 e2 t s1 s2 Hin Hargs.
  pin_name Hin.
  all: first
    [ eapply idx_by_obligation;   [ exact Hin | tauto | exact Hargs ]
    | eapply base_by_obligation;  [ exact Hin | tauto | exact Hargs ]
    | eapply subst_by_obligation; [ exact Hin | tauto | exact Hargs ]
    | eapply pi_by_obligation;    [ exact Hin | tauto | exact Hargs ]
    | eapply proofirr_by_obligation; [ exact Hin | tauto | exact Hargs ]
    | pin_lookup ].
Qed.

(* ------------------------------------------------------------------ *)
(* The model is a model                                                 *)
(* ------------------------------------------------------------------ *)

#[export] Instance Dtt_model_ok
  : CutTModel_ok (V := string) ott_dtt [] (CM := DttCM)
  := DttCM_ok cong_obligation by_obligation.
