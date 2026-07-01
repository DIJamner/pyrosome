Set Implicit Arguments.

(* Integration test: drive the linear-CPS type inference entirely from
   injectivity schemas produced by the e-graph generator
   ([Tools.EGraph.InjRuleGen], equation-saturation mode), instead of the
   hand-written [linear_*_injectivity] lists in [Lang.LinearCPS].

   The generator runs on the (already elaborated) linear language and returns
   [(constructor, injective-arg-names)] schemas; these feed
   [build_injection_rules] exactly as the hand lists did.  The one thing
   injectivity cannot express -- [conc] left-cancellation -- is added on top, as
   before (the generator correctly does NOT report [conc] as injective).

   Success criterion: inference driven by the generated schemas yields a
   well-formed language ([cps_lang_gen_wf]). *)

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Elab.Elab
  Lang.LinearSubst Lang.LinearCPS
  Tools.Matches Tools.Resolution Tools.EGraph.ComputeWf
  Tools.EGraph.TypeInference Tools.EGraph.InjRuleGen
  Tools.EGraph.Automation.
Import Core.Notations.

(* Injectivity schemas from the generator, over the elaborated linear language.
   Replaces linear_cps_injectivity ++ linear_block_subst_injectivity ++
   linear_value_subst_injectivity. *)
Definition linear_gen_schemas :=
  Eval vm_compute in
    gen_schemas 2 (linear_cps_lang ++ linear_block_subst ++ linear_value_subst).

(* Re-infer the surface CPS language, driven by the generated schemas plus the
   [conc] cancellation sequent. *)
Definition linear_cps_lang_gen :=
  Eval vm_compute in
    (infer_lang_ext_simple_gen
       (linear_block_subst ++ linear_value_subst)
       linear_cps_lang_def
       (fun L => build_injection_rules linear_gen_schemas L
                 ++ linear_ext_injectivity)).

(* The generated schemas suffice: inference produces a well-formed language. *)
Lemma cps_lang_gen_wf
  : wf_lang_ext (linear_block_subst ++ linear_value_subst) linear_cps_lang_gen.
Proof. compute_wf_lang. Qed.
