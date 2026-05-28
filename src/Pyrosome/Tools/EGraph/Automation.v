Set Implicit Arguments.

(*TODO: clean up imports*)
From coqutil Require Import Datatypes.String Datatypes.Result.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils Ltac Result.
From Pyrosome Require Import Theory.Core Elab.ElabCompilers.
Import Core.Notations.
(*TODO: repackage this in compilers*)
Import CompilerDefs.Notations.

From Stdlib Require derive.Derive.

From Utils Require Import EGraph.Defs.
From Pyrosome.Tools.EGraph Require Import Defs Theorems.
Import PositiveInstantiation.
From coqutil Require Import Map.Interface.
From Utils Require Import Monad.
From Pyrosome.Tools Require Import PosRenaming.
From Stdlib Require Import NArith.
From Stdlib Require Import Classes.RelationClasses.
Import StateMonad.
Import StringInstantiation.


From Pyrosome Require Import Tools.Matches Tools.Resolution.


Definition print_egraph {X} (g : instance string string string_trie_map string_trie_map string_list_trie_map X) :=
  (NamedList.named_map (NamedList.named_map (entry_value _ X)) (NamedList.named_map map.tuples (map.tuples g.(db))),
    map.tuples g.(equiv).(UnionFind.parent _ _ _)).


Definition subst_weight (r : renaming string) (a : atom positive positive) :=
  if inb (map.get (p_to_v r) a.(atom_fn))
       [Some "val_subst"; Some "blk_subst"] then Some 20%nat
  else Some (length a.(atom_args)).

Definition filter_rules :=
(fun pat : string * Rule.rule string =>
   match pat with
   | (_, term_rule _ _ _) => false
   | _ => true
   end).

Fixpoint term_depth (e : term string) :=
  match e with
  | var _ => 1
  | con _ l => 1 + (fold_left Pos.max (map term_depth l) 1)
  end.

Instance depth_analysis : analysis string string (option positive) :=
  weighted_depth_analysis (fun a => Some 1).

(* ================================================================== *)
(* Phases 4-6 SKELETON for [egraph_sound].                            *)
(*                                                                    *)
(* These are the positive-side (post-renaming) soundness lemmas of    *)
(* the reducing-equal chain, stated so the chain type-checks and the  *)
(* cong -> equal interface is validated.  Bodies are admits to be     *)
(* discharged in the dedicated phases.  Dependency / status notes:    *)
(*                                                                    *)
(*  - egraph_reducing_equal_step_sound (Phase 4): needs Phase 3       *)
(*    saturation soundness (scheduled_saturate_until_sound), plus     *)
(*    are_unified_sound (DONE in QueryOptSound) and add_open_*_sound   *)
(*    (DONE in Theorems).                                              *)
(*  - egraph_reducing_cong_sound (Phase 5): red_fuel induction over    *)
(*    the goal list, using step_sound + extract_weighted_sound +      *)
(*    cong_subgoals_sound.  NOTE the goals are heterogeneously typed   *)
(*    (injectivity congruence creates subgoals at the constructor's    *)
(*    argument sorts), so the statement carries a parallel [types]     *)
(*    list rather than a single sort -- a design point this skeleton   *)
(*    surfaces.                                                        *)
(*  - egraph_reducing_equal_sound (Phase 5c): the singleton corollary, *)
(*    PROVED here from cong_sound (validates that interface).          *)
(*                                                                    *)
(* Still missing for [egraph_sound] itself (left Admitted below):     *)
(*  - the Phase-1 *reverse* renaming bridge (eq_term on positive l'   *)
(*    => eq_term on string l), which does not exist yet; and          *)
(*  - [schedule_sound] is a PLACEHOLDER (the real condition -- each    *)
(*    compiled rule_set sound under lang_model -- is the Phase 3<->6   *)
(*    interface; only optimize_sequent_FORWARD is needed for it).     *)
(* ================================================================== *)
(* Trivial positive-side facts the soundness instantiation needs.
   [positive_Eqb_ok] exists only as a [#[local]] instance in
   PosRenamingProperties, so reprove it here. *)
Lemma positive_Eqb_ok : Eqb_ok positive_Eqb.
Proof. intros a b; unfold eqb, positive_Eqb; destruct (Pos.eqb_spec a b); auto. Qed.

Lemma pos_lt_asym : Asymmetric Pos.lt.
Proof. intros x y h1 h2; exact (Pos.lt_irrefl x (Pos.lt_trans _ _ _ h1 h2)). Qed.

Section ReducingSkeleton.

  Local Notation pos_schedule :=
    (list (nat * rule_set positive positive TrieMap.trie_map TrieMap.trie_map)).
  Local Notation red_cong :=
    (Defs.egraph_reducing_cong TrieMap.ptree_map_plus (@pos_trie_map)
       Pos.succ PosListMap.sort_of (@compat_intersect)).
  Local Notation red_eq_step :=
    (Defs.egraph_reducing_equal_step TrieMap.ptree_map_plus (@pos_trie_map)
       Pos.succ PosListMap.sort_of (@compat_intersect)).

  (* The real Phase-3/6 interface (no longer a placeholder): [sort_of] is
     fresh in [l'] (guaranteed by the renaming, which reserves position 1),
     and every compiled rule_set in [sched] satisfies the saturation
     hypotheses under [lang_model PosListMap.sort_of l'] (Theorems.v's
     [schedule_sound_real]).  Discharged downstream by
     [egraph_reducing_equal'_to_pos] from [build_rule_set] +
     [optimize_sequent_forward] + [pt_spaced_intersect_correct]. *)
  Definition schedule_sound (l' : lang positive) (sched : pos_schedule) : Prop :=
    fresh PosListMap.sort_of l' /\
    @Theorems.schedule_sound_real positive positive_Eqb positive_default
      TrieMap.trie_map TrieMap.ptree_map_plus (@pos_trie_map) Pos.succ
      PosListMap.sort_of Pos.lt (@compat_intersect) l' sched.

  (* The egraph-soundness lemmas require [map.ok] of the egraph's maps.  For
     the positive instantiation these are [map.ok (TrieMap.trie_map A)] (the
     idx/symbol map) and [map.ok (@pos_trie_map A)] (the db trie).  Neither is
     currently proven in the tree -- [trie_map_ok] is [Abort]ed on its
     [fold_spec] (TrieMap.v) and [pos_trie_map] has no [map.ok] at all.  Both
     are taken as assumptions in this inner section (the deferred
     trie-lawfulness obligation), confined here so they do not leak onto
     [schedule_sound] / the wrapper lemmas / [egraph_sound]. *)
  Section StepInst.
    Context (trie_map_ok : forall A, map.ok (TrieMap.trie_map A)).
    Context (pos_trie_map_ok : forall A, map.ok (@pos_trie_map A)).

    Lemma egraph_reducing_equal_step_sound
      (l' : lang positive) (sched : pos_schedule) (rfuel sat_fuel : nat)
      (a b : term positive) (t : sort positive) :
      wf_lang l' -> wf_term l' [] a t -> wf_term l' [] b t ->
      schedule_sound l' sched ->
      let '(res, x1, x2, g) := red_eq_step l' sched rfuel sat_fuel a b in
      res = true -> fst (Defs.are_unified x1 x2 g) = true -> eq_term l' [] t a b.
    Proof.
      intros Hwf Ha Hb [Hfresh Hsched].
      exact (@Theorems.egraph_reducing_equal_step_sound positive positive_Eqb positive_Eqb_ok
               positive_default TrieMap.trie_map TrieMap.ptree_map_plus trie_map_ok
               TrieMap.ptree_map_plus_ok (@pos_trie_map) pos_trie_map_ok
               Pos.succ PosListMap.sort_of Pos.lt
               pos_lt_asym Pos.lt_succ_diag_r Pos.lt_trans
               (@compat_intersect) l' Hwf Hfresh sched rfuel sat_fuel a b t Ha Hb Hsched).
    Qed.
  End StepInst.

  (* The positive instantiation of the (now fully proven, generic)
     congruence-reduction soundness.  It is real -- modulo the same two
     [map.ok] trie-lawfulness assumptions [StepInst] takes -- so it lives in
     an analogous inner section.  This is the concrete demonstration that
     [Theorems.egraph_reducing_equal_sound_generic] applies at positive; the
     clean, assumption-free [egraph_reducing_cong_sound] / [egraph_sound]
     below are kept as-is (so [by_reduction] / Test.v still work) until the
     trie-lawfulness subproject discharges [trie_map_ok] / [pos_trie_map_ok]. *)
  Section CongInst.
    Context (trie_map_ok : forall A, map.ok (TrieMap.trie_map A)).
    Context (pos_trie_map_ok : forall A, map.ok (@pos_trie_map A)).

    Lemma egraph_reducing_equal_sound_pos
      (l' : lang positive) (sched : pos_schedule)
      (rfuel sat_fuel efuel red_fuel : nat) inj
      (e1 e2 : term positive) (t : sort positive) :
      wf_lang l' -> wf_term l' [] e1 t -> wf_term l' [] e2 t ->
      schedule_sound l' sched ->
      PositiveInstantiation.egraph_reducing_equal l' sched inj
        rfuel sat_fuel efuel red_fuel e1 e2 = Success tt ->
      eq_term l' [] t e1 e2.
    Proof.
      intros Hwf He1 He2 [Hfresh Hsched] Hsucc.
      unfold PositiveInstantiation.egraph_reducing_equal,
        Defs.egraph_reducing_equal in Hsucc.
      exact (@Theorems.egraph_reducing_equal_sound_generic positive positive_Eqb positive_Eqb_ok
               positive_default TrieMap.trie_map TrieMap.ptree_map_plus trie_map_ok
               TrieMap.ptree_map_plus_ok (@pos_trie_map) pos_trie_map_ok
               Pos.succ PosListMap.sort_of Pos.lt
               pos_lt_asym Pos.lt_succ_diag_r Pos.lt_trans
               (@compat_intersect) l' Hwf Hfresh sched rfuel sat_fuel efuel red_fuel inj
               e1 e2 t He1 He2 Hsched Hsucc).
    Qed.
  End CongInst.

  Lemma egraph_reducing_cong_sound
    (l' : lang positive) (sched : pos_schedule)
    (rfuel sat_fuel efuel red_fuel : nat) inj
    (goals : list (term positive * term positive)) (types : list (sort positive)) :
    wf_lang l' ->
    length types = length goals ->
    all2 (fun p t => let '(a,b) := p in wf_term l' [] a t /\ wf_term l' [] b t)
         goals types ->
    schedule_sound l' sched ->
    red_cong l' sched rfuel sat_fuel efuel red_fuel inj goals = Success tt ->
    all2 (fun p t => let '(a,b) := p in eq_term l' [] t a b) goals types.
  Proof. Admitted.

  Lemma egraph_reducing_equal_sound
    (l' : lang positive) (sched : pos_schedule)
    (rfuel sat_fuel efuel red_fuel : nat) inj
    (e1 e2 : term positive) (t : sort positive) :
    wf_lang l' -> wf_term l' [] e1 t -> wf_term l' [] e2 t ->
    schedule_sound l' sched ->
    PositiveInstantiation.egraph_reducing_equal l' sched inj
      rfuel sat_fuel efuel red_fuel e1 e2 = Success tt ->
    eq_term l' [] t e1 e2.
  Proof.
    intros Hwf He1 He2 Hsched Hsucc.
    pose proof (@egraph_reducing_cong_sound l' sched rfuel sat_fuel efuel red_fuel
                  inj [(e1,e2)] [t] Hwf eq_refl
                  (conj (conj He1 He2) I) Hsched) as Hcong.
    unfold PositiveInstantiation.egraph_reducing_equal,
      Defs.egraph_reducing_equal in Hsucc.
    specialize (Hcong Hsucc).
    cbn in Hcong. tauto.
  Qed.

  (* Phase 1 (reverse) + Phase 6 bridge.  Bundles: the forward renaming
     (string lang/ctx/terms -> a positive lang [l'] with the ctx folded in
     via ctx_to_rules, preserving wf), the schedule soundness of the built
     rule_sets, the carry-over of the [Is_Success] hypothesis to the positive
     [egraph_reducing_equal], and the REVERSE lifting [eq_term on l'] =>
     [eq_term on l].  The reverse renaming lifting does not exist yet
     (PosRenamingProperties has only the forward direction); that, plus
     wf-preservation through [ctx_to_rules], is the remaining content. *)
  Lemma egraph_reducing_equal'_to_pos
    (l : lang string)
    (filter reversible : string * rule string -> bool)
    (inj_rules : list (ne_list string))
    (rebuild_fuel sat_fuel efuel red_fuel : nat)
    (c : ctx string) (t : sort string) (e1 e2 : term string) :
    wf_lang l ->
    wf_ctx (Model:=core_model l) c ->
    wf_term l c e1 t ->
    wf_term l c e2 t ->
    (* The context names must be disjoint from the language symbols, so that
       [ctx_to_rules c ++ l] is well-formed (a name clash would break
       [all_fresh] of the renamed language).  Not derivable from the other
       hypotheses; in practice discharged by computation. *)
    all (fun x => fresh x l) (map fst c) ->
    Is_Success (fst (egraph_reducing_equal' l filter reversible inj_rules
                       rebuild_fuel sat_fuel efuel red_fuel c e1 e2)) ->
    exists (l' : lang positive) (e1' e2' : term positive) (t' : sort positive)
           (sched : pos_schedule) (inj' : named_list positive (list positive)),
      wf_lang l' /\ wf_term l' [] e1' t' /\ wf_term l' [] e2' t' /\
      schedule_sound l' sched /\
      PositiveInstantiation.egraph_reducing_equal l' sched inj'
        rebuild_fuel sat_fuel efuel red_fuel e1' e2' = Success tt /\
      (eq_term l' [] t' e1' e2' -> eq_term l c t e1 e2).
  Proof. Admitted.

End ReducingSkeleton.

(*TODO: generalize what rules to run *)
Theorem egraph_sound
  (rebuild_fuel sat_fuel efuel red_fuel : nat) l filter
  reversible
  inj_rules
  (c : ctx string) t (e1 e2 : term string)
  : wf_lang l ->
    wf_ctx (Model:=core_model l) c ->
    wf_term l c e1 t ->
    wf_term l c e2 t ->
    all (fun x => fresh x l) (map fst c) ->
    Is_Success (fst (egraph_reducing_equal' l filter reversible inj_rules rebuild_fuel sat_fuel efuel red_fuel c e1 e2)) ->
    eq_term l c t e1 e2.
Proof.
  intros Hl Hc He1 He2 Hdisj Hsucc.
  destruct (@egraph_reducing_equal'_to_pos l filter reversible inj_rules
              rebuild_fuel sat_fuel efuel red_fuel c t e1 e2
              Hl Hc He1 He2 Hdisj Hsucc)
    as (l' & e1' & e2' & t' & sched & inj' & Hwf' & He1' & He2' & Hsched
        & Hsucc' & Hlift).
  apply Hlift.
  eapply egraph_reducing_equal_sound;
    [ exact Hwf' | exact He1' | exact He2' | exact Hsched | exact Hsucc' ].
Qed.

(* TODO: think about variable order for query performance

 *)

(* Discharge [all (fun x => fresh x l) (map fst c)] for concrete [c]/[l]:
   reduce [map fst c] to a literal, split the [all], and solve each
   [fresh x l] by computation. *)
Ltac solve_ctx_lang_disjoint :=
  cbn [map fst all]; repeat first [ exact I | apply conj | compute_fresh ].

(*TODO: call Matches.t' or some other tactic to solve subgoals*)
Ltac by_reduction' reversible inj_rules :=
  (*TODO: check subsumed by egraph reduction
  try reduce;
   *)
    apply (egraph_sound 100 100 100 100 filter_rules reversible inj_rules);
    [prove_by_lang_db| | | | solve_ctx_lang_disjoint | flagged_exact I].


(* TODO: plug inj_rules into tactics *)
Definition empty_inj_rules : list (string * list string) := [].

Ltac by_reduction :=
  by_reduction' (fun _ : string * Rule.rule string => true) empty_inj_rules.

Ltac auto_elab_compiler' reversible inj_rules :=
  cleanup_elab_after
  setup_elab_compiler;
  repeat
     ([>repeat t; cleanup_elab_after try 
                    (try decompose_sort_eq; by_reduction' reversible inj_rules)
      | .. ]).

Ltac auto_elab_compiler :=
  auto_elab_compiler' (fun _ : string * Rule.rule string => true) empty_inj_rules.

(* for building filters from lists in tactics *)
Definition rule_named_in l :=
  (fun p : string * Rule.rule string => inb (fst p) l).

(*******************************
 Extraction facilities.

Operations on the same egraph should use a single `weight` paremeter.
Weight is a function from atoms (representing a single level of an AST) to values in the range [0,oo],
representing infinity as None, where a value of infinity means that term will never be extracted.

 *******************************)
Import StringInstantiation.

Notation instance := (instance string string string_trie_map string_trie_map string_list_trie_map (option positive)).

Definition empty_egraph := (empty_egraph (idx:=string) (default : string)
                              (symbol:=string) (symbol_map := string_trie_map)
                              (idx_map := string_trie_map) (option positive)).

Definition add_ctx weight l :=
  add_ctx (V:= string) (V_map := string_trie_map) string_succ "@sort_of" l (H:=weighted_depth_analysis weight) true.

Definition add_open_term weight l :=
  add_open_term (V:= string) (V_map := string_trie_map) string_succ "@sort_of" l (H:=weighted_depth_analysis weight) true.

Definition add_open_sort weight l :=
  add_open_sort (V:= string) (V_map := string_trie_map) string_succ "@sort_of" l (H:=weighted_depth_analysis weight) true.

Definition rebuild weight fuel : state instance _ := (rebuild (idx:=string) fuel (symbol:=string) (H:=weighted_depth_analysis weight)).

Notation extract_weighted := (extract_weighted (V:=string) (V_map:=string_trie_map) (V_trie:=string_list_trie_map)).
