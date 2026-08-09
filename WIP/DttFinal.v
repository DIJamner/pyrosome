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
  WIP.DttModelStruct WIP.DttModelAll WIP.DttNormalization WIP.DttRSubOk.
Import Core.Notations.

(* =====================================================================
   NORMALIZATION FOR THE OTT DEPENDENT TYPE THEORY.

   [ott_dtt] is

       ott_subst_commute ++ ott_pi ++ ott_nat ++ ott_base
         ++ subst_ott ++ ott_info                            (73 rules)

   -- a Tarski universe (U/El, two levels, relevance tags) with dependent
   products, both proof-relevant and proof-irrelevant, with BETA AND ETA,
   Nat, Empty and its eliminator, over a parameterized substitution
   calculus with explicit substitutions.

   The statements below are the parameterised ones of WIP/DttRSubOk.v and
   WIP/DttNormalization.v with their two obligation families discharged by
   WIP/DttModelAll.v.  They are unconditional.
   ===================================================================== *)

(* ------------------------------------------------------------------ *)
(* The model                                                            *)
(* ------------------------------------------------------------------ *)

Definition DttCM_is_ok : CutTModel_ok (V := string) ott_dtt [] (CM := DttCM)
  := DttCM_ok cong_obligation by_obligation.

(* ------------------------------------------------------------------ *)
(* Normalization                                                        *)
(* ------------------------------------------------------------------ *)

(* Every well-typed term of the theory, in a normal environment at a
   normal type, is PROVABLY EQUAL to an eta-long normal form. *)
Theorem ott_dtt_normalization G i A e
  : EnvOk G -> TyOk G i A ->
    wf_term ott_dtt [] e (sExp G i A) ->
    HasNf G i A e.
Proof.
  apply (DttRSubOk.ott_dtt_normalization cong_obligation by_obligation).
Qed.

(* The same for types: every well-formed type is a reducible type, hence
   has a normal representative. *)
Theorem ott_dtt_ty_normalization G i A
  : EnvOk G -> wf_term ott_dtt [] A (sTy G i) -> RTyN G i A.
Proof.
  apply (DttRSubOk.ott_dtt_ty_normalization cong_obligation by_obligation).
Qed.

(* And for environments, where the model's content IS the normalization
   statement. *)
Theorem ott_dtt_env_normalization G
  : wf_term ott_dtt [] G sEnv -> HasNfEnv G.
Proof.
  apply (DttNormalization.ott_dtt_env_normalization
           cong_obligation by_obligation).
Qed.

(* ------------------------------------------------------------------ *)
(* The equational form                                                  *)
(* ------------------------------------------------------------------ *)

(* Provably equal terms receive equal content -- this is the statement the
   whole [CutTModel] route is organised around, and normalization is its
   diagonal. *)
Theorem ott_dtt_eq_sound t e1 e2
  : eq_term ott_dtt [] t e1 e2 -> Ceq_term t e1 e2.
Proof.
  apply (DttNormalization.ott_dtt_eq_sound cong_obligation by_obligation).
Qed.
