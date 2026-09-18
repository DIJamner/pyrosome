(* The end-to-end polymorphic pipeline.

   Putting the pieces together (PLAN-poly.md decision 9):

     poly source term  e            (wf in [poly_source_multilanguage])
        --[ compile PCMP ]-->       (PolyMultilangCompiler.v: the compiler
                                     [PCMP = poly_multilang_compiler ++
                                     polymorphic_interoperating_langs_compiler]
                                     is preserving, so the compiled term is
                                     wf in [poly_target_multilanguage] and
                                     source equalities are preserved)
        --[ mono ]-->               (Monomorphize.v: type-level partial
                                     evaluation, sound and wf-preserving by
                                     construction)
        --[ elim_typerec ]-->       (TyperecPartialEval.v: elimination of the
                                     boundary recursor, landing in
                                     [target_multilanguage_without_typerec])

   The first two steps are unconditional theorems.  The third is *not*:
   monomorphization is not complete -- System F is not monomorphizable in
   general -- so the last step is guarded by a pair of decidable per-program
   side conditions on the monomorphized term:

     [all_typerecs_simple_b (mono c) = true]                 and
     [WfTransfer.avoids ["btrec"; "bAll"] (mono c) = true].

   Both are boolean checks, so for a concrete program they are discharged by
   computation (see [ex1_end_to_end] / [ex3_end_to_end] below, which use the
   checks already computed in Monomorphize.v).  [ex2] of Monomorphize.v is
   the negative example: it *exports* a polymorphic function, its [#"ttd"]
   boundary sits at a bound type variable that no instantiation ever
   reaches, and [all_typerecs_simple_b] on it is [false].                  *)

Set Implicit Arguments.

Require Import Datatypes.String Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.

From Pyrosome Require Import Compilers.Compilers Compilers.SemanticsPreservingDef
  Compilers.CompilerFacts Elab.ElabCompilers.
Import CompilerDefs.Notations.
From Pyrosome Require Import Theory.Core Elab.Elab Tools.Matches Tools.Resolution.
Import Core.Notations.

From Pyrosome.Theory Require Import WfTransfer.

From Pyrosome.Lang.Multilanguages Require Import
  PolyBoundaries PolySource PolyTrecTerms PolyMultilangCompiler
  TyperecPartialEval Monomorphize.

Local Notation term := (@Term.term string).
Local Notation sort := (@Term.sort string).

Local Notation semantics_preserving tgt cmp :=
  (semantics_preserving (tgt_Model := core_model tgt)
     (compile cmp)
     (compile_sort cmp)
     (compile_ctx cmp)
     (compile_args cmp)
     (compile_subst cmp)).

(* ---------------- 1. semantic consequences of compiler preservation ------- *)

Lemma psml_semantics_preserving
  : semantics_preserving poly_target_multilanguage PCMP
      poly_source_multilanguage.
Proof.
  unfold PCMP.
  apply inductive_implies_semantic; try typeclasses eauto;
    eauto using ModelImpls.core_model_ok; try reflexivity.
  1: apply ModelImpls.core_model_ok; try typeclasses eauto.
  1: solve [prove_by_lang_db].
  1: solve [prove_by_lang_db].
  apply poly_source_multilanguage_compiler_preserving.
Qed.

Corollary compiled_wf : forall e t,
    wf_term poly_source_multilanguage [] e t ->
    wf_term poly_target_multilanguage [] (compile PCMP e) (compile_sort PCMP t).
Proof.
  intros e t H.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 psml_semantics_preserving))))) as Hw.
  unfold term_wf_preserving_sem in Hw.
  specialize (Hw [] e t H ltac:(constructor)).
  cbv beta iota zeta delta [core_model] in Hw.
  cbn [compile_ctx] in Hw. exact Hw.
Qed.

Corollary compiled_eq : forall t e1 e2,
    eq_term poly_source_multilanguage [] t e1 e2 ->
    eq_term poly_target_multilanguage [] (compile_sort PCMP t)
      (compile PCMP e1) (compile PCMP e2).
Proof.
  intros t e1 e2 H.
  pose proof (proj1 (proj2 psml_semantics_preserving)) as He.
  unfold term_eq_preserving_sem in He.
  cbv beta iota zeta delta [core_model] in He.
  apply (He []); eauto with lang_core utils.
Qed.

(* ---------------- 2. the end-to-end theorem ---------------- *)

Theorem poly_pipeline : forall e t,
    wf_term poly_source_multilanguage [] e t ->
    let c := compile PCMP e in
    let t' := compile_sort PCMP t in
    eq_term poly_target_multilanguage [] t' c (mono c)
    /\ wf_term poly_target_multilanguage [] (mono c) t'
    /\ (all_typerecs_simple_b (mono c) = true ->
        WfTransfer.avoids string ["btrec"; "bAll"] (mono c) = true ->
        eq_term poly_target_multilanguage [] t' c (elim_typerec (mono c))
        /\ wf_term target_multilanguage_without_typerec [] (elim_typerec (mono c)) t').
Proof.
  intros e t H; cbn zeta.
  pose proof (compiled_wf H) as Hc.
  split; [ exact (mono_sound Hc) |].
  split; [ exact (mono_wf Hc) |].
  intros Hsimple Havoid.
  exact (conj (mono_elim_eq Hc Hsimple Havoid)
              (mono_elim_wf Hc Hsimple Havoid)).
Qed.

(* ---------------- 3. the examples, fully discharged ---------------- *)

(* [ex1]: the polymorphic identity instantiated at [#"bool"], applied to
   [#"T"], sent to the dynamic side.  Both side conditions hold, so the
   whole pipeline runs to completion. *)
Theorem ex1_end_to_end
  : eq_term poly_target_multilanguage [] (compile_sort PCMP ex_star_sort)
      (compile PCMP ex1) (mono (compile PCMP ex1))
    /\ wf_term poly_target_multilanguage [] (mono (compile PCMP ex1))
         (compile_sort PCMP ex_star_sort)
    /\ eq_term poly_target_multilanguage [] (compile_sort PCMP ex_star_sort)
         (compile PCMP ex1) (elim_typerec (mono (compile PCMP ex1)))
    /\ wf_term target_multilanguage_without_typerec []
         (elim_typerec (mono (compile PCMP ex1))) (compile_sort PCMP ex_star_sort).
Proof.
  destruct (poly_pipeline (elab_term_implies_wf ex1_wf)) as [H1 [H2 H3]].
  destruct (H3 ex1_simple ex1_avoids) as [H4 H5].
  exact (conj H1 (conj H2 (conj H4 H5))).
Qed.

(* [ex3]: a *polymorphic* to-dynamic function, instantiated at [#"bool"];
   its boundary only becomes concrete after monomorphization. *)
Theorem ex3_end_to_end
  : eq_term poly_target_multilanguage [] (compile_sort PCMP ex_star_sort)
      (compile PCMP ex3) (mono (compile PCMP ex3))
    /\ wf_term poly_target_multilanguage [] (mono (compile PCMP ex3))
         (compile_sort PCMP ex_star_sort)
    /\ eq_term poly_target_multilanguage [] (compile_sort PCMP ex_star_sort)
         (compile PCMP ex3) (elim_typerec (mono (compile PCMP ex3)))
    /\ wf_term target_multilanguage_without_typerec []
         (elim_typerec (mono (compile PCMP ex3))) (compile_sort PCMP ex_star_sort).
Proof.
  destruct (poly_pipeline (elab_term_implies_wf ex3_wf)) as [H1 [H2 H3]].
  destruct (H3 ex3_simple ex3_avoids) as [H4 H5].
  exact (conj H1 (conj H2 (conj H4 H5))).
Qed.
