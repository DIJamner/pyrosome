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

(* TODO (file 4 body): the fundamental lemma
     wf_term ott [] e t -> reducible e   (and the eq_term -> RedTm PER side),
   by Pyrosome cut-elimination on canonical derivations.  Discharges the
   deferred under'-lift correctness and the Π reflect/reify eta crux. *)
