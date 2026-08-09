Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Ltac.
From Pyrosome Require Import Theory.Core Tools.Matches.
From Pyrosome.Tools.EGraph Require Import Automation ComputeWf.
Require Import Pyrosome.Gluing.Dtt.Syntax.
Import Core.Notations.

(* =====================================================================
   WHY THE INDEX SPELLINGS DISAGREE, AND THE CHEAP WAY TO BRIDGE THEM.

   [tlvl] has two equations, "next0" ([next L0 = iota L1]) and "next1"
   ([next L1 = inf]), and the compiled rules of [ott_dtt] do NOT agree on
   which representative to use.  Neighbouring rules disagree, and so do a
   term rule and its own substitution equation:

     "Nat"         concludes at [info rel (next L0)]
     "Nat subst"   concludes at [info rel (iota L1)]
     "Empty"       concludes at [info rel (iota L1)]
     "Empty subst" concludes at [info rel (next L0)]
     "Pi_irr", "Pi_irr subst" and "Pi_irr beta" put the codomain code [B]
       at [info rel (iota L1)]; "lam_irr" and "app_irr" put it at
       [info rel (next L0)].

   THIS IS NOT AN AUTHORING BUG, AND WRITING THE IDEAL REPRESENTATION DOES
   NOT FIX IT.  Lang/OTT/Nat.v already writes [info rel (next L0)]
   uniformly, in all four of the Nat/Empty rules above.  The reason it does
   not survive: [Elab.PreRule]'s [infer_rule] does not treat the written
   conclusion sort as authoritative.  It loads the sort into an e-graph,
   saturates against the language's equations, and re-EXTRACTS a
   representative using [TypeInference.mk_weight], which charges 1 per
   non-hole atom.  [info rel (next L0)] and [info rel (iota L1)] both cost
   4, so the winner is an arbitrary tie-break -- and it depends on the
   AMBIENT LANGUAGE, not on what the rule says.  Both checked directly:

     - [infer_rule (ott_base ++ subst_ott ++ ott_info) inj] applied to the
       "Empty" rule returns [info rel (next L0)] whether the prerule is
       written with [next L0] or with [iota L1] -- the two elaborate to the
       IDENTICAL rule;
     - inside Nat.v's [Derive], where the base has grown by Nat/zero/suc and
       their substitution equations, the same rule comes out [iota L1].

   Fixing it at the source would therefore mean either hand-elaborating the
   affected rules and adding them with [push_rule] (as Lang/OTT/Pi.v does
   for eta), or changing the extraction weight in
   Tools/EGraph/TypeInference.v -- which would re-elaborate every language
   in the project.

   The cheap alternative is to let the e-graph do the bridging, which it
   does in well under a second and axiom-free.  [egraph_eq] below is the
   tactic; the concrete conversion lemmas built on it -- [eq_info_next0],
   [eq_sort_ty_cong], [eq_sort_exp_cong], [eq_sort_exp_ty],
   [wft_U0irr_next], [wft_U0irr_iota] -- live in src/Pyrosome/Gluing/Dtt/NfTyping.v, next to the
   typing lemmas that consume them.
   ===================================================================== *)

(* Discharge an [eq_term ott_dtt c e1 e2] goal with concrete [c], [e1], [e2]
   by running the e-graph.  [solve_wf_ctx] and [compute_term_wf] both open
   with [assumption] against a [wf_lang ott_dtt] fact, hence the leading
   [pose proof].  As elsewhere in this development the check itself is
   deferred to [Qed] (it is implemented with [vm_cast_no_check]), so a
   BROKEN goal looks like it went through until [Qed] actually runs. *)
Ltac egraph_eq :=
  pose proof ott_dtt_wf;
  apply (egraph_sound 100 100 100 100 filter_rules
           (fun _ : string * Rule.rule string => true) empty_inj_rules);
  [ exact ott_dtt_wf | solve_wf_ctx | compute_term_wf | compute_term_wf
  | flagged_exact I ].

(* The two index equations, done the cheap way.  Both "next0" and "next1"
   have EMPTY rule contexts, so these carry no hypotheses at all.  Measured:
   0.005 s of tactic time and 0.7 s at [Qed], each, axiom-free. *)

Lemma eq_tlvl_next0 : eq_term ott_dtt [] sTlvl (oNext oL0) (oIota oL1).
Proof. unfold sTlvl, oNext, oL0, oIota, oL1. egraph_eq. Qed.

Lemma eq_tlvl_next1 : eq_term ott_dtt [] sTlvl (oNext oL1) oInf.
Proof. unfold sTlvl, oNext, oL1, oInf. egraph_eq. Qed.

Lemma eq_info_iota1
  : eq_term ott_dtt [] sInfo (iCode oL0) (oInfo oRel (oIota oL1)).
Proof.
  unfold sInfo, iCode, oInfo, oRel, oNext, oL0, oIota, oL1. egraph_eq.
Qed.

Lemma eq_info_inf
  : eq_term ott_dtt [] sInfo (iCode oL1) (oInfo oRel oInf).
Proof.
  unfold sInfo, iCode, oInfo, oRel, oNext, oL1, oInf. egraph_eq.
Qed.
