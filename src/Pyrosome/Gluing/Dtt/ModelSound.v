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
  Pyrosome.Gluing.Dtt.ModelStruct.
Import Core.Notations.

(* =====================================================================
   DTT NORMALIZATION, LAYER 4c: the top-level theorems.

   Everything here is stated against the two obligation families that are
   still open ([CongObligation] and [ByObligation], src/Pyrosome/Gluing/Dtt/ModelStruct.v),
   so that the ENDGAME IS PINNED DOWN AND MACHINE-CHECKED before those
   land: this file proves that the normalization statement follows from
   exactly those two and nothing else.  The other eight [CutTModel_ok]
   fields, and [DttCM_ok]'s assembly from all ten, are already done and
   axiom-free.

   Discharging the two parameters is then the whole remaining task, and
   these theorems become unconditional by [exact].
   ===================================================================== *)

Section WithObligations.
  Context (Hcong : CongObligation) (Hby : ByObligation).

  #[local] Definition Dtt_ok : CutTModel_ok (V := string) ott_dtt [] (CM := DttCM)
    := DttCM_ok Hcong Hby.

  #[local] Existing Instance Dtt_ok.

  (* ---------------------------------------------------------------- *)
  (* The fundamental theorem, specialized                              *)
  (* ---------------------------------------------------------------- *)

  (* [Ceq_term] is [Prop]-valued, so the [inhabited] CutModelSound returns
     is erasable -- the single [Prop]/[Type] bridge of the development,
     exactly as in the simply-typed proof. *)

  Theorem ott_dtt_eq_sound t e1 e2
    : eq_term ott_dtt [] t e1 e2 -> Ceq_term t e1 e2.
  Proof.
    intro Heq.
    destruct (cut_model_inhabited (l := ott_dtt) ott_dtt_wf (c := [])
                wf_ctx_nil (CM := DttCM) Heq) as [H].
    exact H.
  Qed.

  Theorem ott_dtt_wf_sound t e
    : wf_term ott_dtt [] e t -> Ceq_term t e e.
  Proof.
    intro Hwf; apply ott_dtt_eq_sound, eq_term_refl; exact Hwf.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* What that says, unfolded                                          *)
  (* ---------------------------------------------------------------- *)

  (* At a term sort, the model's content is: under every reducible
     substitution into a normal environment, the instance is reducible at
     every normal representative of the instantiated type.  Reading that
     back at the identity substitution is what turns it into "has a normal
     form", and that last step is Layer 3's [RSub_id]. *)
  Corollary ott_dtt_exp_sound G i A e
    : wf_term ott_dtt [] e (sExp G i A) ->
      forall D g, EnvOk D -> RSubN D G g ->
        RTmN D i (oTySubst D G g i A) (oExpSubst D G g i A e).
  Proof.
    intro Hwf; apply (proj2 (Ceq_exp_e (ott_dtt_wf_sound Hwf))).
  Qed.

  (* Types: every reducible instance of a well-formed type is a reducible
     type -- i.e. has a normal representative carrying a candidate. *)
  Corollary ott_dtt_ty_sound G i A
    : wf_term ott_dtt [] A (sTy G i) ->
      forall D g, EnvOk D -> RSubN D G g -> RTyN D i (oTySubst D G g i A).
  Proof.
    intro Hwf; apply (proj2 (Ceq_ty_e (ott_dtt_wf_sound Hwf))).
  Qed.

  (* Environments: every well-formed environment has a normal form.  This
     one needs nothing further -- it is already the normalization
     statement at the sort [env]. *)
  Corollary ott_dtt_env_normalization G
    : wf_term ott_dtt [] G sEnv -> HasNfEnv G.
  Proof.
    intro Hwf; apply (proj2 (Ceq_env_e (ott_dtt_wf_sound Hwf))).
  Qed.

  (* Substitutions: a well-formed substitution carries reducible
     substitutions to reducible substitutions. *)
  Corollary ott_dtt_sub_sound G G' g
    : wf_term ott_dtt [] g (sSub G G') ->
      forall D h, EnvOk D -> RSubN D G h -> RSubN D G' (oCmp D G G' h g).
  Proof.
    intro Hwf; apply (proj2 (Ceq_sub_e (ott_dtt_wf_sound Hwf))).
  Qed.

End WithObligations.
