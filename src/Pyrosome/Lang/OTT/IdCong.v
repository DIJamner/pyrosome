From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import
  Theory.Core Elab.Elab
  Elab.PreRule
  Tools.ComputeWf
  Tools.Matches
  Tools.Resolution
  Tools.Interactive.

From Pyrosome.Lang Require Import
  Subst SubstEqnGen.
From Pyrosome.Lang.OTT Require Import
  Base Nat Pi SubstCommute ProofIrr IdCore IdComp IdFunextIrr IdFunextRel.

Import Core.Notations.

(* ======================================================================= *)
(* The heterogeneous observational identity type: ASSEMBLY.                 *)
(*                                                                          *)
(* The fragment is authored in three pieces and concatenated here.  The     *)
(* split is a PERFORMANCE measure, and the numbers are the justification:   *)
(* [compute_wf_rule] checks each rule against its PREFIX, and its cost      *)
(* grows sharply with that prefix.  The 3-binder function-extensionality    *)
(* rule was measured at 1h55m against a two-rule prefix, and had not        *)
(* finished after 2h35m against the full one.                               *)
(*                                                                          *)
(*   IdCore.v    ott_id_core    Id, Id subst                     (~35 s)    *)
(*   IdComp.v    ott_id_comp    Idcong + the computation rules   (~4 min)   *)
(*   IdFunextDefs.v  the two rule DEFINITIONS only              (1.3 s)    *)
(*   IdFunextIrr.v   2-binder funext  } SIBLINGS over a common   (~12 min)  *)
(*   IdFunextRel.v   3-binder funext  } base, neither in the      (~2h13m)  *)
(*                                      other's prefix                      *)
(*   IdCong.v    ott_id_cong = funext_rel ++ funext_irr ++ comp ++ core     *)
(*                                                                          *)
(* The payoff is not the first build, it is every later one: editing a      *)
(* computation rule no longer re-triggers the two-hour funext check.        *)
(*                                                                          *)
(* Two constraints shape the decomposition, and neither is negotiable.      *)
(*                                                                          *)
(* (1) [ott_id_comp] must be derived over a base WITHOUT the funext rules.  *)
(*     With a funext rule in scope, [infer_rule] re-elaborates "Id-Nat-00"  *)
(*     to a DIFFERENT rule -- verified directly, the two inferred rules     *)
(*     compare unequal, and inference costs 5.6x more.  That is the         *)
(*     [next L0] <-> [iota L1] flip Gluing/Dtt/Syntax.v warns about, and it *)
(*     would silently invalidate the rule shapes baked into Eqns.v / Wf.v / *)
(*     Model*.v.  Deriving [ott_id_comp] and [ott_id_funext] over a COMMON  *)
(*     base keeps each one's elaboration exactly as it is.                  *)
(*                                                                          *)
(* (2) Consequently the two extensions are SIBLINGS, not a chain, so one of *)
(*     them has to be lifted to its position in the assembled language.     *)
(*     [Core.lang_ext_monotonicity] does exactly that: a rule verified      *)
(*     against a smaller prefix stays well-formed against a larger one.     *)
(*     We lift [ott_id_funext], so [ott_id_comp] keeps the prefix it was    *)
(*     checked against and only the (already paid for) funext rules move.   *)
(*                                                                          *)
(* Downstream sees exactly what it saw before: [ott_id_cong] together with  *)
(* [ott_id_cong_wf : wf_lang_ext ott_id_base ott_id_cong].                  *)
(* ======================================================================= *)

(* Composition of two extensions.  [wf_lang_ext lp ((n,r)::l)] demands
   [wf_rule (l ++ lp) r], so stacking an extension of [l1 ++ lp] on top of an
   extension of [lp] is exactly an associativity shuffle. *)
Lemma wf_lang_ext_compose (lp l1 l2 : lang)
  : wf_lang_ext lp l1 ->
    wf_lang_ext (l1 ++ lp) l2 ->
    wf_lang_ext lp (l2 ++ l1).
Proof.
  intros H1 H2; induction H2; basic_goal_prep; auto.
  constructor; auto;
    rewrite <- app_assoc; assumption.
Qed.

Definition ott_id_cong := Eval vm_compute in
  (ott_id_funext_rel ++ ott_id_funext_irr ++ ott_id_comp ++ ott_id_core).

Lemma ott_id_cong_wf : wf_lang_ext ott_id_base ott_id_cong.
Proof.
  replace ott_id_cong
    with (ott_id_funext_rel ++ (ott_id_funext_irr ++ (ott_id_comp ++ ott_id_core)))
    by (vm_compute; reflexivity).
  (* Each piece was checked against the smallest prefix it needs, and is lifted
     into position here.  The three lifts are the whole point of the split. *)
  apply wf_lang_ext_compose;
    [ apply wf_lang_ext_compose;
      [ apply wf_lang_ext_compose;
        [ exact ott_id_core_wf | exact ott_id_comp_wf ]
      | (* funext_irr: checked over core ++ base *)
        eapply lang_ext_monotonicity;
        [ exact ott_id_funext_irr_wf
        | unfold incl; intros; rewrite ?in_app_iff in *; tauto
        | apply use_compute_all_fresh; vm_compute; exact I ] ]
    | (* funext_rel: also checked over core ++ base, NOT over funext_irr *)
      eapply lang_ext_monotonicity;
      [ exact ott_id_funext_rel_wf
      | unfold incl; intros; rewrite ?in_app_iff in *; tauto
      | apply use_compute_all_fresh; vm_compute; exact I ] ].
Qed.

#[local] Definition ott_id_cong_entry := lang_entry ott_id_cong_wf.
#[export] Hint Resolve ott_id_cong_entry : wf_lang_db.
