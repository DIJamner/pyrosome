(* ============================================================== *)
(* Soundness of scheduled saturation.                             *)
(*                                                                *)
(* Carved out of Theorems.v (the SchedSat section) to keep that   *)
(* file smaller, following the companion-section style of         *)
(* AddCtxInversion.v: this file Requires Theorems (and Defs) and  *)
(* re-opens a parallel [Section WithVar] with the same Context.   *)
(* The SchedSat body references only constants from Utils.EGraph.*)
(* and Pyrosome.Tools.EGraph.Defs (saturate_until[_sound],        *)
(* process_const_rules, run1iter_rule_hyps, list_Miter_breakable, *)
(* scheduled_saturate_until, ...), all imported normally — so no  *)
(* Theorems section-closed constants need re-exposure.  No proof  *)
(* bodies change.                                                 *)
(* ============================================================== *)
From Stdlib Require Import Lists.List Classes.RelationClasses BinNums.
Import ListNotations.
Open Scope list.


From coqutil Require Import Map.Interface Datatypes.Result.

From Utils Require Import Utils UnionFind Monad ExtraMaps VC Relations Result.
From Utils.EGraph Require Import Defs Semantics QueryOpt SemanticsParents SemanticsAreUnified SemanticsSaturate SemanticsUnionSem SemanticsLSurvive SemanticsRebuildCanon SemanticsAnalysesCover SemanticsHashDb.
Import Monad.StateMonad.
From Pyrosome.Theory Require Import Core ModelImpls.
From Pyrosome.Theory Require WfCutElim.
Import Core.Notations.
From Pyrosome.Tools.EGraph Require Import Defs.
From Pyrosome.Tools.EGraph Require Import Theorems.


#[local] Hint Resolve Properties.map.extends_refl : utils.
#[local] Hint Rewrite combine_map_fst_snd : utils.


Section WithVar.
  Context (V : Type)
    {V_Eqb : Eqb V}
    {V_Eqb_ok : Eqb_ok V_Eqb}
    {V_default : WithDefault V}.

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation subst := (@subst V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).

  Notation eq_subst l :=
    (eq_subst (Model:= core_model l)).
  Notation eq_args l :=
    (eq_args (Model:= core_model l)).
  Notation wf_subst l :=
    (wf_subst (Model:= core_model l)).
  Notation wf_args l :=
    (wf_args (Model:= core_model l)).
  Notation wf_ctx l :=
    (wf_ctx (Model:= core_model l)).


  Context
    (V_map : forall A, map.map V A)
      (V_map_plus : ExtraMaps.map_plus V_map)
      (V_map_ok : forall A, map.ok (V_map A))
      (V_trie : forall A, map.map (list V) A)
      (V_trie_ok : forall A, map.ok (V_trie A)).

  Notation instance := (instance V V V_map V_map V_trie).

  Notation atom := (atom V V).


  Context (succ : V -> V).

  (* Include sort_of as special symbol/fn in db. *)
  Context (sort_of : V).

  Context (lt : V -> V -> Prop).

  Context (lt_asymmetric : Asymmetric lt)
    (lt_succ : forall x, lt x (succ x))
    (lt_trans : Transitive lt).

  (* ============================================================== *)
  (* Soundness of scheduled saturation                              *)
  (* ============================================================== *)
  (* Wraps Semantics' saturate_until_sound up through the Pyrosome   *)
  (* scheduled_saturate_until loop, against an arbitrary model m.    *)
  (* The Phase-4 caller instantiates m := lang_model.  The per-      *)
  (* rule_set side conditions [rs_saturation_hyps] are the real      *)
  (* content of schedule_sound, discharged in Phase 6.               *)
  Section SchedSat.
    Context (V_map_plus_ok : ExtraMaps.map_plus_ok V_map).
    Context (X : Type) `{analysis V V X}.
    Context (spaced_list_intersect
              : forall B, WithDefault B -> (B -> B -> B) ->
                          ne_list (V_trie B * list bool) -> V_trie B).
    Context (m : model V) (Hm : model_ok V m).

    Local Notation instance := (Utils.EGraph.Defs.instance V V V_map V_map V_trie X).
    Local Notation egraph_ok := (egraph_ok V lt V V_map V_map V_trie X).
    Local Notation sound := (egraph_sound_for_interpretation V V V_map V_map V_trie X m).

    (* The per-rule_set side conditions saturation needs: process_const_rules
       is sound (const-rule analogue of erule_sound; deferred Hconst), and every
       compiled rule satisfies run1iter's per-rule bundle against any snapshot. *)
    Definition rs_saturation_hyps (rs : rule_set V V V_map V_map) : Prop :=
      (forall e i, egraph_ok e -> sound i e ->
         egraph_ok (snd (process_const_rules V V_Eqb succ V_default V V_map V_map V_trie X rs e))
         /\ exists i', map.extends i' i /\ sound i' (snd (process_const_rules V V_Eqb succ V_default V V_map V_map V_trie X rs e)))
      /\ (forall e r, In r (compiled_rules V V V_map V_map rs) ->
            run1iter_rule_hyps V V_Eqb V_default V V_map V_map_plus V_map V_map_plus V_trie X spaced_list_intersect m rs e r).

    (* One pass of the schedule (list_Miter_breakable, stopping at the first
       entry whose termination check fires) is sound: each entry runs
       saturate_until on its rule_set, sound by saturate_until_sound, and the
       interpretations compose. *)
    Lemma list_Miter_breakable_sound (rfuel : nat) (p : state instance bool)
      (HP : forall e i, egraph_ok e -> sound i e -> egraph_ok (snd (p e)) /\ sound i (snd (p e))) :
      forall (sched : list (nat * rule_set V V V_map V_map)),
      (forall n rs, In (n, rs) sched -> rs_saturation_hyps rs) ->
      forall i e, egraph_ok e -> sound i e ->
      match list_Miter_breakable (fun entry => saturate_until succ V_default (analysis_result:=X) spaced_list_intersect rfuel (snd entry) p (fst entry)) sched e with
      | (_, e') => egraph_ok e' /\ exists i', map.extends i' i /\ sound i' e'
      end.
    Proof.
      induction sched as [|entry sched' IH]; intros Hsched i e Hok Hsnd.
      - cbn [list_Miter_breakable Mret StateMonad.state_monad].
        split; [exact Hok|]. exists i. split; [apply Properties.map.extends_refl | exact Hsnd].
      - cbn [list_Miter_breakable Mbind Mret StateMonad.state_monad].
        destruct entry as [fuel_i rs_i].
        cbn [fst snd].
        destruct (Hsched fuel_i rs_i (or_introl eq_refl)) as [Hconst_i Hrules_i].
        pose proof (@saturate_until_sound V V_Eqb V_Eqb_ok lt succ V_default V V_Eqb V_Eqb_ok
                      V_map V_map_plus V_map_plus_ok V_map_ok V_map V_map_plus V_map_ok
                      V_trie V_trie_ok X V_map_plus_ok spaced_list_intersect _ m Hm
                      lt_asymmetric lt_succ lt_trans rfuel rs_i p HP Hconst_i Hrules_i fuel_i i e Hok Hsnd) as Hsat.
        destruct (saturate_until succ V_default (analysis_result:=X) spaced_list_intersect rfuel rs_i p fuel_i e) as [break e1] eqn:Hsu.
        destruct Hsat as (Hok1 & i1 & Hext1 & Hsnd1).
        destruct break.
        + split; [exact Hok1|]. exists i1. split; [exact Hext1 | exact Hsnd1].
        + assert (Hsched' : forall n rs, In (n, rs) sched' -> rs_saturation_hyps rs)
            by (intros n rs Hin; apply (Hsched n rs); right; exact Hin).
          pose proof (IH Hsched' i1 e1 Hok1 Hsnd1) as HIH.
          destruct (list_Miter_breakable (fun entry => saturate_until succ V_default (analysis_result:=X) spaced_list_intersect rfuel (snd entry) p (fst entry)) sched' e1) as [b e2] eqn:Hlmb.
          destruct HIH as (Hok2 & i2 & Hext2 & Hsnd2).
          split; [exact Hok2|]. exists i2.
          split; [eapply map_extends_trans; [exact Hext2 | exact Hext1] | exact Hsnd2].
    Qed.

    (* The scheduled saturation loop is sound: fuel induction, each round one
       schedule pass (list_Miter_breakable_sound); interpretations compose. *)
    Lemma scheduled_saturate_until_sound (rfuel : nat) (p : state instance bool)
      (HP : forall e i, egraph_ok e -> sound i e -> egraph_ok (snd (p e)) /\ sound i (snd (p e)))
      (schedule : list (nat * rule_set V V V_map V_map))
      (Hsched : forall n rs, In (n, rs) schedule -> rs_saturation_hyps rs)
      (fuel : nat) :
      forall i e, egraph_ok e -> sound i e ->
      match scheduled_saturate_until V_map_plus succ spaced_list_intersect rfuel schedule p fuel e with
      | (_, e') => egraph_ok e' /\ exists i', map.extends i' i /\ sound i' e'
      end.
    Proof.
      induction fuel as [|fuel IH]; intros i e Hok Hsnd.
      - cbn [scheduled_saturate_until Mret StateMonad.state_monad].
        split; [exact Hok|]. exists i. split; [apply Properties.map.extends_refl | exact Hsnd].
      - cbn [scheduled_saturate_until Mbind Mret StateMonad.state_monad].
        pose proof (list_Miter_breakable_sound rfuel p HP schedule Hsched i e Hok Hsnd) as Hlmb.
        destruct (list_Miter_breakable (fun entry => saturate_until succ V_default (analysis_result:=X) spaced_list_intersect rfuel (snd entry) p (fst entry)) schedule e) as [done e1] eqn:Hlmb_eq.
        destruct Hlmb as (Hok1 & i1 & Hext1 & Hsnd1).
        destruct done.
        + split; [exact Hok1|]. exists i1. split; [exact Hext1 | exact Hsnd1].
        + pose proof (IH i1 e1 Hok1 Hsnd1) as HIH.
          destruct (scheduled_saturate_until V_map_plus succ spaced_list_intersect rfuel schedule p fuel e1) as [b e2] eqn:Hss.
          destruct HIH as (Hok2 & i2 & Hext2 & Hsnd2).
          split; [exact Hok2|]. exists i2.
          split; [eapply map_extends_trans; [exact Hext2 | exact Hext1] | exact Hsnd2].
    Qed.

  End SchedSat.
End WithVar.
