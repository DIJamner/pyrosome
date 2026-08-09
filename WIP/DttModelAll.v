Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
From Pyrosome.Gluing Require Import CutTModel Eval CutModelSound.
Require Import WIP.DttSyntax WIP.DttNf WIP.DttLR WIP.DttRSub WIP.DttCeq
  WIP.DttModelStruct WIP.DttModelIdx WIP.DttModelBase WIP.DttModelSubst
  WIP.DttModelPi.
Import Core.Notations.

(* =====================================================================
   LAYER 4b, ASSEMBLED.

   The 64 rule obligations were proved in four fragments, each with a
   dispatcher in the right field shape but restricted to its own rule
   names:

     WIP/DttModelIdx.v    the index formers        9 cong,  3 eq
     WIP/DttModelBase.v   universe and base types  6 cong,  6 eq
     WIP/DttModelSubst.v  the substitution calculus 10 cong, 13 eq
     WIP/DttModelPi.v     the binders               7 cong, 10 eq
                                                  ---------------
                                                   32 cong, 32 eq

   This file checks that those name restrictions PARTITION the language --
   every one of [ott_dtt]'s 32 term rules and 32 equations is claimed by
   exactly one fragment -- and assembles [CongObligation] and
   [ByObligation].  With those, [DttCM_ok] is unconditional and so is
   normalization.
   ===================================================================== *)

(* The [In] premise is a concrete disjunction over a closed 73-element
   list, so [vm_compute] pins it and the case split enumerates the rules;
   each case then names its own fragment, and the wrong fragments fail on
   the name disjunct rather than silently succeeding. *)
Theorem cong_obligation : CongObligation.
Proof.
  intros c' name args t s1 s2 Hin Hargs.
  pose proof Hin as Hin'.
  vm_compute in Hin'.
  repeat (destruct Hin' as [Hin'|Hin']); try (exfalso; exact Hin');
    inversion Hin'; subst.
  all: first
    [ eapply idx_cong_obligation;   [ exact Hin | tauto | exact Hargs ]
    | eapply base_cong_obligation;  [ exact Hin | tauto | exact Hargs ]
    | eapply subst_cong_obligation; [ exact Hin | tauto | exact Hargs ]
    | eapply pi_cong_obligation;    [ exact Hin | tauto | exact Hargs ] ].
Qed.

Theorem by_obligation : ByObligation.
Proof.
  intros c' name e1 e2 t s1 s2 Hin Hargs.
  pose proof Hin as Hin'.
  vm_compute in Hin'.
  repeat (destruct Hin' as [Hin'|Hin']); try (exfalso; exact Hin');
    inversion Hin'; subst.
  all: first
    [ eapply idx_by_obligation;   [ exact Hin | tauto | exact Hargs ]
    | eapply base_by_obligation;  [ exact Hin | tauto | exact Hargs ]
    | eapply subst_by_obligation; [ exact Hin | tauto | exact Hargs ]
    | eapply pi_by_obligation;    [ exact Hin | tauto | exact Hargs ] ].
Qed.

(* ------------------------------------------------------------------ *)
(* The model is a model                                                 *)
(* ------------------------------------------------------------------ *)

#[export] Instance Dtt_model_ok
  : CutTModel_ok (V := string) ott_dtt [] (CM := DttCM)
  := DttCM_ok cong_obligation by_obligation.
