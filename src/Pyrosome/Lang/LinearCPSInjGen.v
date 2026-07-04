Set Implicit Arguments.

(* Integration test: drive the linear-CPS type inference entirely from the
   functional-dependency schemas produced by the e-graph generator
   ([Tools.EGraph.InjRuleGen], equation-saturation mode), instead of the
   hand-written [linear_*_injectivity] lists (and the bespoke
   [linear_ext_injectivity] cancellation sequent) in [Lang.LinearCPS].

   [gen_fundep_schemas] runs one general procedure over the elaborated language:
   for every constructor and every argument position it searches for the minimal
   set of sibling positions on which agreement forces agreement at that position
   (a functional dependency of the constructor's e-class).  The empty set is
   ordinary injectivity; a nonempty set is cancellation.  Nothing is special-
   cased -- [conc]'s left/right cancellation laws fall out of the SAME search
   that produces every injectivity rule, because [conc] is non-injective yet
   cancellative.  The schemas feed [build_general_injection_rules].

   Success criterion: inference driven entirely by these generated schemas yields
   a well-formed language ([cps_lang_gen_wf]). *)

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

(* Functional-dependency schemas from the general generator, over the elaborated
   linear language.  Replaces linear_cps_injectivity ++
   linear_block_subst_injectivity ++ linear_value_subst_injectivity AND the
   hand-written linear_ext_injectivity cancellation sequent.

   Fuel is 3 (not the 2 that suffices for injectivity alone): at fuel 2 the
   equation saturation has not yet collapsed the [conc emp ...] unit towers, so a
   *spurious* counterexample suppresses [conc]'s LEFT cancellation
   ([conc G H1 = conc G H2 -> H1 = H2], shared first arg) -- exactly the law the
   inference needs to recover the implicit env from a [blk (conc G H)] result
   sort.  One more saturation step removes the spurious counterexample and the
   left cancellation appears; the schema set is otherwise identical to fuel 2. *)
Definition linear_gen_schemas :=
  Eval vm_compute in
    gen_fundep_schemas 3 (linear_cps_lang ++ linear_block_subst ++ linear_value_subst).

(* Re-infer the surface CPS language, driven solely by the generated schemas. *)
Definition linear_cps_lang_gen :=
  Eval vm_compute in
    (infer_lang_ext_simple_gen
       (linear_block_subst ++ linear_value_subst)
       linear_cps_lang_def
       (build_general_injection_rules linear_gen_schemas)).

(* The generated schemas suffice: inference produces a well-formed language. *)
Lemma cps_lang_gen_wf
  : wf_lang_ext (linear_block_subst ++ linear_value_subst) linear_cps_lang_gen.
Proof. compute_wf_lang. Qed.
