(* Phase 2 target: discharge the transport interface [sort_transport_at]
   (Theory/SyntacticSortCovering.v) for the polymorphic / existential
   languages, so they can drop sort_of atoms from compiled rule queries.

   ============================ STATUS ============================

   The original conjecture

     syntactic_sort_eq_langb' l = true -> wf_lang l -> sort_transport_at l []

   is FALSE — machine-checked refutation in WIP/TransportCounterexample.v.
   The union-form ungated condition (every equation ctx var occurs in
   fv(e1) ++ fv(e2)) pins each variable in SOME side, but an eq_sort/eq_term
   TRANS-chain can route through a middle term that introduces a variable
   pinned by NEITHER endpoint (e.g. [x:S] |- g x = a and [x:S] |- g x = b give
   a == b in [x:S] through the middle g x).  If the variable's sort has no
   closed inhabitant, the chain cannot be replayed in the empty context, while
   both endpoint images are perfectly wf.  This is the SubstWfCounterexample
   inhabitation phenomenon surfacing one level deeper: through equation-ctx
   variables that DO occur in the equation, but on one side only.

   The corrected conjecture below adds the missing ingredient: closed
   inhabitation of every (closed, wf) index-headed sort.  This defeats the
   vacuity trick: it makes every index-fragment context satisfiable, so
   garbage middles are repairable in principle.

   ======================= PROOF OBSTACLES ========================

   Even with [index_inhabited], sufficiency is NOT established.  Known
   obstacles, from the failed proof designs:

   1. THE TRANS/MIDDLE PROBLEM is fixable by a one-sided motive
      (M := forall s, wf_sort [] (T[/s/]) ->
              (wf left image  -> transported eq (which yields right-image wf))
            /\ (wf right image -> transported eq)),
      which handles refl/sym/trans/conv cleanly.

   2. THE REAL WALL is eq_sort_subst / eq_term_subst: the outer image wf pins
      the instance substitution sigma∘s only at OCCURRENCE positions; the
      entry IHs (from the eq_subst subderivation) need DECLARED-sort image wf.
      The occurrence-vs-declared eq_sort comes from wf-derivation inversion —
      an OPAQUE derivation, not a subderivation, so structural induction gives
      no IH for it.  This occurrence->declared upgrade is exactly the
      min-sorts covering problem itself: [sort_transport_at] is the root of a
      recursion that must be self-justifying.  Under syntactic sorts it
      grounds out (t = t'); in general no well-founded measure is known.
      Candidate route: induction on the SIZE OF THE CLOSED IMAGES (the
      inversion-produced eq_sorts live between sort-images that are proper
      subterms of the original images), with canonical-inhabitant repair
      bounded in size; the interplay is delicate and unverified.

   3. Index-fragment restriction: with no sort_eq_rule and ungated index
      equations, every equation reachable from index sorts has an all-index
      ctx (occurrence sorts of its vars are index-headed by the closure, and
      declared sorts share heads with occurrence sorts by eq_sort_head_det).
      So the recursion stays inside the (inhabited) index fragment — needed
      to even state the repair.

   Per-side pinning (ctx vars in fv(e_i) ++ fv_sort(t) for EACH side i) makes
   the chain-replay proof go through WITHOUT inhabitation (each step re-pins
   from the current side, so middles stay wf) — but it REJECTS the poly
   stack: projection/eta/terminal laws (ty_snoc_hd's g, snoc-wkn-beta's A,
   cmp_forget's g) discard information by design.  Substitution calculi
   fundamentally need the inhabitation-aware condition.

   ===================== ARCHITECTURAL NOTE =======================

   The runtime gate can stay a boolean (syntactic_sort_eq_langb'); the
   SOUNDNESS side-condition [index_inhabited] is a Prop discharged
   per-language at the AdapterGlue instantiation (poly: ty_env by ty_emp;
   env by emp; ty by All-closure; ty_sub by forget/snoc + canonical tys —
   each an induction over closed ty_env terms). *)

Set Implicit Arguments.
From Stdlib Require Import Lists.List.
Import ListNotations.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core SyntacticSorts SyntacticSortCovering.
Import Core.Notations.

Section WithVar.
  Context (V : Type)
    {V_Eqb : Eqb V}
    {V_Eqb_ok : Eqb_ok V_Eqb}
    {V_default : WithDefault V}.

  Notation lang := (@lang V).
  Notation sort := (@sort V).
  Notation term := (@term V).

  (* Closed inhabitation of the index fragment: every closed wf index-headed
     sort has a closed inhabitant.  Defeats the vacuity counterexample
     (WIP/TransportCounterexample.v), where an empty sort gates a chain
     middle.  Discharged per-language (semantic, not boolean). *)
  Definition index_inhabited (l : lang) : Prop :=
    forall t, wf_sort l [] t ->
              index_head l (sort_head t) ->
              exists e, wf_term l [] e t.

  (* ================================================================
     CONJECTURE (open).  The refutation in WIP/TransportCounterexample.v
     shows [index_inhabited] (or something like it) is NECESSARY; its
     SUFFICIENCY is unproven and the known proof designs hit the
     occurrence->declared wall described in the header.  Do NOT flip the
     e-graph gate on the strength of this Admitted.
     ================================================================ *)
  Lemma syntactic_sort_eq_langb'_transport_at (l : lang)
    : syntactic_sort_eq_langb' l = true ->
      index_inhabited l ->
      wf_lang l ->
      sort_transport_at l [].
  Proof.
  Admitted.

End WithVar.
