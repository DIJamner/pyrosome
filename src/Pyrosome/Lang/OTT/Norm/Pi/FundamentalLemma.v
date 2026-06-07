(* ====================================================================== *)
(* OTT pivot, file 4/5 (see WIP/NEXT_SESSION.md UPDATE-v).                  *)
(*                                                                        *)
(* The FUNDAMENTAL LEMMA for the reduction-on-syntax logical relation:      *)
(* every well-typed OTT type/term is reducible.  This is also where the     *)
(* DEFERRED correctness of the LogicalRelation.v Kripke builders            *)
(* (act_code/cod_at/ounder/mapp) gets exercised against the real OTT typing *)
(* and the OTT substitution equations.                                     *)
(*                                                                        *)
(* FOUNDATION (this commit): assemble the concrete OTT language             *)
(*   ott := ott_pi ++ ott_nat ++ ott_base ++ subst_ott ++ ott_info         *)
(* and prove `wf_lang ott`, so the generic LR (over `wf_lang l`) can be     *)
(* instantiated at `l := ott`.  The fundamental lemma itself is TODO.       *)
(* ====================================================================== *)
From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Tools Require Import Matches.
From Pyrosome.Lang.OTT Require Import Base Nat Pi.
From Pyrosome.Lang.OTT.Norm.Pi Require Import Reduction Neutral LogicalRelation.
Import Core.Notations.

(* The concrete cut-free OTT language with proof-relevant Π, ℕ/Empty, the
   substitution calculus and the static info layer.  (No Id/Cast/Σ — those are
   not needed for the Π normalization payoff.)  The Π β/η computation rules live
   inside `ott_pi` itself, so this is exactly the language the reduction relation
   orients. *)
Definition ott : lang string :=
  (ott_pi ++ ott_nat ++ ott_base ++ subst_ott ++ ott_info)%list.

(* NB: `ott_wf` inherits the project-wide `Automation.egraph_sound` axiom from the
   imported OTT language wf proofs (`ott_pi_wf`/`ott_nat_wf`/`ott_base_wf`/...),
   which are established via the e-graph wf checker.  The LR machinery itself
   (Reduction/Neutral/LogicalRelation) is axiom-free; only the concrete OTT lang
   instantiation carries `egraph_sound`. *)
Lemma ott_wf : wf_lang ott.
Proof.
  unfold ott.
  (* lower stack, bottom-up via wf_lang_concat. *)
  pose proof ott_info_wf as H0.
  pose proof (wf_lang_concat H0 subst_ott_wf) as H1.
  pose proof (wf_lang_concat H1 ott_base_wf) as H2.
  pose proof (wf_lang_concat H2 ott_nat_wf) as H3.
  (* ott_pi is ext over (ott_base ++ ..), weaken it over (ott_nat ++ ott_base ++ ..). *)
  assert (Hpi : wf_lang_ext (ott_nat ++ ott_base ++ subst_ott ++ ott_info)%list ott_pi).
  { eapply lang_ext_monotonicity.
    - exact ott_pi_wf.
    - apply incl_appr, incl_refl.
    - compute_all_fresh. }
  exact (wf_lang_concat H3 Hpi).
Qed.

(* ====================================================================== *)
(* WELL-TYPEDNESS OF THE LogicalRelation.v KRIPKE BUILDERS (subgoal (a)).    *)
(*                                                                        *)
(* The reducibility relation's Pi case carries Kripke operations            *)
(* (`act_code`, `extc`, `cod_at`, `mapp`, ...) that push the domain /        *)
(* codomain codes and the member along an object substitution.  Their        *)
(* DEFINITIONS landed in LogicalRelation.v with correctness DEFERRED here     *)
(* (UPDATE-v): until `wf_lang ott` and the OTT substitution equations are in  *)
(* scope, one cannot check that the inlined `exp_subst`/`under'` annotations  *)
(* actually type.  This section discharges those obligations one builder at   *)
(* a time, against the real `ott` typing rules.                              *)
(* ====================================================================== *)

(* The standard "build a `wf_term`/`wf_args` derivation by hand" driver,      *)
(* specialised to `ott`: peel `wf_args`, expose the model's `wf_term`,        *)
(* compute the `with_names_from` substitution in each subject's sort, close   *)
(* variable leaves by assumption and constructor leaves by `wf_term_by'`      *)
(* (which keeps the conclusion type flexible, so the `with_names_from`        *)
(* unification is deferred to a reflexivity/conversion side-goal).            *)
Ltac ott_wf_args :=
  repeat first
    [ simple apply wf_args_nil
    | simple eapply wf_args_cons2
    | simple eapply wf_args_cons
    | progress cbn [Model.wf_term core_model]
    | progress compute_wf_subjects
    | eassumption
    | (eapply Elab.wf_term_by';
         [ apply named_list_lookup_err_in; compute; reflexivity
         |
         | left; compute; reflexivity ]) ].

(* The "U subst" computation rule instantiated by an EXPLICIT (variable-only)
   substitution, packaged so its `wf_subst` side-goal is discharged from the
   variable hypotheses by `assumption` rather than the computational wf checker
   (which cannot evaluate the free env/level/sub variables).  This is the bare
   convertibility `ty_subst g (U rF lF G) = U rF lF D` the builder typings need. *)
Lemma U_subst_eq rF lF g G D
  (HG : wf_term ott [] G (scon "env" []))
  (HD : wf_term ott [] D (scon "env" []))
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (Hg : wf_term ott [] g (scon "sub" [G; D]))
  : eq_term ott [] (scon "ty" [code_info lF; D])
      (con "ty_subst" [oU rF lF G; code_info lF; g; G; D]) (oU rF lF D).
Proof.
  pose proof ott_wf as Hwf.
  pose (s := [("l", lF); ("r", rF); ("g", g); ("G'", G); ("G", D)] : subst string).
  (* recast the explicit conclusion as the "U subst" rule's t/e1/e2 under s,
     so `eq_term_subst` applies without inverting the substitution. *)
  change (eq_term ott []
    ({{s #"ty" "G" (#"info" #"rel" (#"next" "l")) }} [/s/])
    ({{e #"ty_subst" "G" "G'" "g" (#"info" #"rel" (#"next" "l")) (#"U" "G'" "r" "l") }} [/s/])
    ({{e #"U" "G" "r" "l" }} [/s/])).
  eapply eq_term_subst.
  - eapply eq_term_by with (name := "U subst").
    apply named_list_lookup_err_in; compute; reflexivity.
  - apply eq_subst_refl. unfold s.
    repeat first
      [ simple apply wf_subst_nil | simple eapply wf_subst_cons
      | progress cbn [Model.wf_term core_model] | progress compute_wf_subjects
      | eassumption ].
  - eapply rule_in_ctx_wf with (name := "U subst").
    + exact Hwf.
    + apply named_list_lookup_err_in; compute; reflexivity.
    + compute; reflexivity.
Qed.

(* `act_code rF lF g G D F` pushes the domain code `F : exp G (U rF lF)`      *)
(* along an object substitution `g : sub D G`, landing a code in env `D`.     *)
(* The naive result type `exp D _ (ty_subst g (U rF lF G))` is converted to   *)
(* `exp D _ (U rF lF D)` via the "U subst" computation rule, so downstream    *)
(* `extc`/`cod_at` see a bare `U`-code. *)
Lemma act_code_wf rF lF g G D F
  (HG : wf_term ott [] G (scon "env" []))
  (HD : wf_term ott [] D (scon "env" []))
  (HrF : wf_term ott [] rF (scon "relevance" []))
  (HlF : wf_term ott [] lF (scon "lvl" []))
  (Hg : wf_term ott [] g (scon "sub" [G; D]))
  (HF : wf_term ott [] F (scon "exp" [oU rF lF G; code_info lF; G]))
  : wf_term ott [] (act_code rF lF g G D F)
                   (scon "exp" [oU rF lF D; code_info lF; D]).
Proof.
  pose proof ott_wf as Hwf.
  unfold act_code, oexp_subst.
  eapply wf_term_conv.
  - eapply wf_term_by.
    + apply named_list_lookup_err_in; compute; reflexivity.
    + ott_wf_args.
  - (* the naive `exp_subst` result type `exp D _ (ty_subst g (U rF lF G))`
       converts to the target `exp D _ (U rF lF D)`: reduce the substitution
       into the result sort, split by congruence, and the only non-reflexive
       component is the "U subst" computation rule. *)
    cbn [with_names_from sort_subst apply_subst substable_sort
         Substable.apply_subst0 term_substable].
    sort_cong.
    all: cbn [Model.eq_term core_model].
    all: first
      [ solve [ eapply eq_term_refl; ott_wf_args ]
      | solve [ match goal with
                | |- eq_term ?l ?c ?t ?lhs ?rhs =>
                    let t2 := eval vm_compute in t in
                    let lhs2 := eval vm_compute in lhs in
                    change (eq_term l c t2 lhs2 rhs)
                end;
                apply U_subst_eq; assumption ] ].
Qed.

(* TODO (file 4 body, continued):
   - remaining builder typings: `extc`, `act_member`, `act_cod`, `cod_at`,
     `mapp` (the `ounder` under'-lift is the genuinely fiddly one — its
     correctness is exactly the OTT "Pi_rel subst" under' annotation).
   - then the fundamental lemma proper:
       wf_term ott [] e t -> reducible e   (and the eq_term -> RedTm PER side),
     by Pyrosome cut-elimination on canonical derivations; discharges the
     Pi reflect/reify eta crux. *)
