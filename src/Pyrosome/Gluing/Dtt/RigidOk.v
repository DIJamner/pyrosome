Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
From Pyrosome.Gluing Require Import CutTModel Eval CutModelSound.
Require Import Pyrosome.Gluing.Dtt.Syntax Pyrosome.Gluing.Dtt.NormalForms Pyrosome.Gluing.Dtt.Rigid.
Import Core.Notations.

(* =====================================================================
   LAYER 0.5b, PART 2: the rigid model is a model, and what that buys.

   src/Pyrosome/Gluing/Dtt/Rigid.v discharges all ten [CutTModel_ok] obligations for
   [RigCM] separately.  This file assembles them and runs the fundamental
   theorem (Gluing/CutModelSound.v), yielding the ONE fact the rigidity
   argument needs from the semantic side:

     provably equal terms have equal rigid interpretations.

   Everything downstream of Layer 0.5 consumes only [rigid_sound] and its
   four sort-specific corollaries.
   ===================================================================== *)

(* ------------------------------------------------------------------ *)
(* The model is a model                                                 *)
(* ------------------------------------------------------------------ *)

(* Built with [constructor] and ten [exact]s rather than a [{| ... |}]
   record literal: elaborating the literal against [CutTModel_ok]
   stack-overflows (~44s, then death), while this is instant.  The same
   trick is needed for the main model's assembly. *)
#[export] Instance RigCM_ok : CutTModel_ok ott_dtt [] (CM := RigCM).
Proof.
  constructor.
  - exact var_obligation.
  - exact cong_obligation.
  - exact by_obligation.
  - exact term_trans_obligation.
  - exact term_sym_obligation.
  - exact term_conv_obligation.
  - exact sort_cong_obligation.
  - exact sort_by_obligation.
  - exact sort_trans_obligation.
  - exact sort_sym_obligation.
Defined.

(* ------------------------------------------------------------------ *)
(* The fundamental theorem, specialized                                 *)
(* ------------------------------------------------------------------ *)

(* [rceq_term] is [Prop]-valued (it is accepted as a [Type]-valued carrier
   by cumulativity), so the [inhabited] that CutModelSound hands back is
   erasable here. *)
Theorem rigid_sound t e1 e2
  : eq_term ott_dtt [] t e1 e2 -> rceq_term t e1 e2.
Proof.
  intro Heq.
  destruct (cut_model_inhabited (l := ott_dtt) ott_dtt_wf (c := [])
              wf_ctx_nil (CM := RigCM) Heq) as [H].
  exact H.
Qed.

(* ------------------------------------------------------------------ *)
(* The four readings                                                    *)
(* ------------------------------------------------------------------ *)

Corollary rigid_env G1 G2
  : eq_term ott_dtt [] sEnv G1 G2 -> Req_env G1 G2.
Proof. apply rigid_sound. Qed.

Corollary rigid_ty G i A1 A2
  : eq_term ott_dtt [] (sTy G i) A1 A2 -> Req_ty G A1 A2.
Proof. apply rigid_sound. Qed.

Corollary rigid_sub G G' g1 g2
  : eq_term ott_dtt [] (sSub G G') g1 g2 -> Req_sub G G' g1 g2.
Proof. apply rigid_sound. Qed.

(* At an [exp] sort the model only says anything when the type is
   universe-like -- which is exactly the code fragment, and exactly what
   rigidity is about. *)
Corollary rigid_code G r l c1 c2
  : eq_term ott_dtt [] (sCode G r l) c1 c2 -> Req_code G c1 c2.
Proof.
  intro Heq.
  pose proof (rigid_sound Heq) as H.
  unfold sCode in H.
  rewrite rceq_exp_eq, USkel_U in H.
  exact H.
Qed.
