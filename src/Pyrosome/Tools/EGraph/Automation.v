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
From Utils Require Import FullPosTrie FullPosTrieConv TrieMapFold.
From Utils Require Import EGraph.QcAlignment.
From Pyrosome.Tools.EGraph Require Import Defs Theorems ReducingCong.
Import PositiveInstantiation.
From coqutil Require Import Map.Interface.
From Utils Require Import Monad Result.
From Pyrosome.Tools Require Import PosRenaming PosRenamingProperties RenamingBridge.
From Pyrosome.Tools.EGraph Require Import RenamingCoincide.
From Pyrosome.Tools.EGraph Require Import AdapterGlue.
From Pyrosome.Theory Require ClosedCore.
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

Definition filter_rules {V} :=
(fun pat : V * Rule.rule V =>
   match pat with
   (* Filtering out sort rules has a risk because some rules need sorts to match.
      However, it is a huge performance improvement.
    *)
   | (_, sort_rule _ _)
   | (_, term_rule _ _ _) => false
   | _ => true
   end).

Fixpoint term_depth (e : term string) :=
  match e with
  | var _ => 1
  | con _ l => 1 + (fold_left Pos.max (map term_depth l) 1)
  end.

Instance depth_analysis : analysis string string (option positive) :=
  weighted_size_analysis (fun a => Some 1).

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
    (Defs.egraph_reducing_cong TrieMap.ptree_map_plus (@FullPosTrie.full_pos_trie_map)
       Pos.succ Pos.leb PosListMap.sort_of (@fpt_spaced_intersect)).
  Local Notation red_eq_step :=
    (Defs.egraph_reducing_equal_step TrieMap.ptree_map_plus (@FullPosTrie.full_pos_trie_map)
       Pos.succ Pos.leb PosListMap.sort_of (@fpt_spaced_intersect)).

  (* The real Phase-3/6 interface (no longer a placeholder): [sort_of] is
     fresh in [l'] (guaranteed by the renaming, which reserves position 1),
     and every compiled rule_set in [sched] satisfies the saturation
     hypotheses under [lang_model PosListMap.sort_of l'] (Theorems.v's
     [schedule_sound_real]).  Discharged downstream by
     [egraph_reducing_equal'_to_pos] from [build_rule_set] +
     [optimize_sequent_forward] + [pt_spaced_intersect_correct]. *)
  Definition schedule_sound (l' : lang positive) (sched : pos_schedule) : Prop :=
    fresh PosListMap.sort_of l' /\
    @ReducingCong.schedule_sound_real positive positive_Eqb positive_default
      TrieMap.trie_map TrieMap.ptree_map_plus (@FullPosTrie.full_pos_trie_map) Pos.succ Pos.leb
      PosListMap.sort_of Pos.lt (@fpt_spaced_intersect) l' sched.

  (* The egraph-soundness lemmas require [map.ok] of the egraph's maps.  For
     the positive instantiation these are [map.ok (TrieMap.trie_map A)] (the
     idx/symbol map) and [map.ok (@full_pos_trie_map A)] (the db trie).  BOTH
     are now proven in the tree -- [TrieMapFold.trie_map_ok] and
     [FullPosTrie.full_pos_trie_map_ok], the latter the lawful fattened
     (3-constructor) carrier the positive instantiation switched to (the db
     trie is [full_pos_trie_map], the query-side join goes through
     [fpt_spaced_intersect], a conversion wrapper over [compat_intersect]).  So
     these soundness lemmas are now UNCONDITIONAL (no trie-lawfulness
     assumption left to confine). *)
  (* The positive instantiation of the (now fully proven, generic)
     congruence-reduction soundness, UNCONDITIONAL via the two real [map.ok]
     instances above. *)
  (* Bridge: the generic congruence lemma concludes a per-goal EXISTENTIAL-sort
     equality ([In (a,b) goals -> exists s, eq_term l [] s a b]); recover the
     [all2]-at-the-declared-types shape by coercing each existential sort to the
     goal's type [t] (sorts of a term are unique up to [eq_sort], via
     [term_sorts_eq]). *)
  Lemma all2_eq_term_of_in
    (l' : lang positive) (wfl : wf_lang l')
    (goals : list (term positive * term positive)) (types : list (sort positive)) :
    length types = length goals ->
    all2 (fun p t => let '(a,b) := p in wf_term l' [] a t /\ wf_term l' [] b t)
         goals types ->
    (forall a b, In (a,b) goals -> exists s, eq_term l' [] s a b) ->
    all2 (fun p t => let '(a,b) := p in eq_term l' [] t a b) goals types.
  Proof.
    pose proof positive_Eqb_ok as Heqbok.
    revert types.
    induction goals as [|[a b] goals' IH]; intros [|t types'] Hlen Hwf Hin;
      cbn [all2] in *; try discriminate; try exact I.
    destruct Hwf as [Hwfab Hwf'].
    destruct Hwfab as [Hwfa Hwfb].
    split.
    - destruct (Hin a b (or_introl eq_refl)) as [s Heq].
      assert (Hwfas : wf_term l' [] a s) by exact (eq_term_wf_l wfl wf_ctx_nil Heq).
      exact (eq_term_conv Heq (term_sorts_eq wfl wf_ctx_nil Hwfas Hwfa)).
    - apply IH; [ cbn [Datatypes.length] in Hlen; congruence | exact Hwf' | ].
      intros a0 b0 Hin0. exact (Hin a0 b0 (or_intror Hin0)).
  Qed.

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
  Proof.
    intros Hwf Hlen Hall2 [Hfresh Hsched] Hsucc.
    (* Per-goal wf premise required by the generic lemma. *)
    assert (Hwfgoals : forall a b, In (a,b) goals ->
              (exists ta, wf_term l' [] a ta) /\ (exists tb, wf_term l' [] b tb)).
    { clear Hsucc Hsched Hfresh.
      revert types Hlen Hall2.
      induction goals as [|[a b] goals' IH]; intros [|t types'] Hlen Hall2 a0 b0 Hin;
        cbn [all2 In] in *; try contradiction; try discriminate.
      destruct Hall2 as [Hwfab Hall2'].
      destruct Hwfab as [Hwfa Hwfb].
      destruct Hin as [Heq | Hin'].
      - inversion Heq; subst; clear Heq. split; eexists; eassumption.
      - exact (IH types' ltac:(cbn [Datatypes.length] in Hlen; congruence)
                 Hall2' a0 b0 Hin'). }
    (* Apply the generic congruence soundness at the positive instantiation. *)
    pose proof (@ReducingCong.egraph_reducing_cong_sound positive positive_Eqb positive_Eqb_ok
                  positive_default TrieMap.trie_map TrieMap.ptree_map_plus (@TrieMapFold.trie_map_ok)
                  TrieMap.ptree_map_plus_ok (@FullPosTrie.full_pos_trie_map) (@FullPosTrie.full_pos_trie_map_ok)
                  Pos.succ Pos.leb PosListMap.sort_of Pos.lt
                  pos_lt_asym Pos.lt_succ_diag_r Pos.lt_trans
                  (@fpt_spaced_intersect) l' Hwf Hfresh sched rfuel sat_fuel efuel Hsched
                  red_fuel inj goals Hwfgoals Hsucc) as Hconc.
    exact (@all2_eq_term_of_in l' Hwf goals types Hlen Hall2 Hconc).
  Qed.

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
     [eq_term on l].

     The whole renaming bridge is now WIRED (and machine-checked): the proof
     destructures the renaming state monad, applies [rename_egraph_bridge]
     (forward wf + bound/unrename facts) and [reverse_eq_term_lift]
     (unrename-then-eq_rtv), with [RenamingCoincide] bridging the EGraph maps
     to the ClosedCore ones.  The ONLY remaining gap is the [schedule_sound]
     conjunct ([admit] below) -- the Phase-6 obligation that the two built
     rule_sets are sound under [lang_model] (build_rule_set +
     optimize_sequent_forward + pt_spaced_intersect_correct). *)
  Lemma egraph_reducing_equal'_to_pos
    (l : lang string)
    (lf reversible : string * rule string -> bool)
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
    Is_Success (fst (egraph_reducing_equal' l lf reversible inj_rules
                       rebuild_fuel sat_fuel efuel red_fuel c e1 e2)) ->
    exists (l' : lang positive) (e1' e2' : term positive) (t' : sort positive)
           (sched : pos_schedule) (inj' : named_list positive (list positive)),
      wf_lang l' /\ wf_term l' [] e1' t' /\ wf_term l' [] e2' t' /\
      schedule_sound l' sched /\
      PositiveInstantiation.egraph_reducing_equal l' sched inj'
        rebuild_fuel sat_fuel efuel red_fuel e1' e2' = Success tt /\
      (eq_term l' [] t' e1' e2' -> eq_term l c t e1 e2).
  Proof.
    intros Hwf Hwfc He1 He2 Hdisj Hsucc.
    (* The disjointness premise discharges [egraph_reducing_equal']'s freshness
       guard, so the computation takes its [then] branch. *)
    assert (Hguard : Is_true (forallb (fun x => freshb x l) (map fst c))).
    { apply Is_true_forallb. revert Hdisj. apply all_wkn.
      intros x _ Hx. apply (proj2 (freshb_spec _ _)). exact Hx. }
    (* Destructure the renaming computation into its 6 sequential steps. *)
    unfold egraph_reducing_equal' in Hsucc.
    destruct (forallb (fun x => freshb x l) (map fst c)) eqn:Hgeq;
      [ clear Hguard Hgeq | destruct Hguard ].
    cbn [Mbind Mret state_monad] in Hsucc.
    destruct (rename_lang (ctx_to_rules c ++ l)
                {| p_to_v := map.empty; v_to_p := []; next_id := xO xH |})
      as [Lp r1] eqn:HrL.
    destruct (rename_term (var_to_con e1) r1) as [E1p r2] eqn:HrE1.
    destruct (rename_term (var_to_con e2) r2) as [E2p r3] eqn:HrE2.
    destruct (rename_lang (ctx_to_rules c ++ filter lf l) r3) as [posR r4] eqn:HrPR.
    destruct (rename_lang (ctx_to_rules c ++ named_map rev_rule
                (filter (fun p => reversible p && lf p) l)) r4) as [posRR r5] eqn:HrPRR.
    destruct (list_Mmap rename_inj inj_rules r5) as [injp r6] eqn:HrInj.
    cbn [fst] in Hsucc.
    (* The rebuild-success guard (Defs.egraph_reducing_equal'): [build_rule_set]
       returns [Failure] when a rule's assumption rebuild ran out of fuel, so
       [Is_Success] forces both rule_sets to be [Success].  Expose them; the
       failing branches contradict [Is_Success], and the Success/Success branch
       reduces the guard match back to the bare [egraph_reducing_equal] run for
       the carry-over below.  [Hbrs1]/[Hbrs2] are kept for discharging
       [schedule_sound]. *)
    destruct (PositiveInstantiation.build_rule_set rebuild_fuel posR Lp)
      as [rsR|e_st1] eqn:Hbrs1; [ | cbn in Hsucc; destruct Hsucc ].
    destruct (PositiveInstantiation.build_rule_set rebuild_fuel posRR Lp)
      as [rsRR|e_st2] eqn:Hbrs2; [ | cbn in Hsucc; destruct Hsucc ].
    cbv beta iota in Hsucc.
    (* Rename the goal sort [sort_var_to_con t] at [r3] -> [Tp]/[r7].  (The sort
       is not renamed by the computation; [t'] is our existential choice.) *)
    destruct (rename_sort (sort_var_to_con t) r3) as [Tp r7] eqn:HrT.
    (* The closed source data is well-formed (via [ctx_to_rules_wf] / [wf_term_vtr],
       with the EGraph maps rewritten to the ClosedCore ones). *)
    assert (HwfLcl : wf_lang (ctx_to_rules c ++ l)) by
      (rewrite ctx_to_rules_coincide; apply (wf_lang_concat Hwf);
       apply ClosedCore.ctx_to_rules_wf; first [assumption | typeclasses eauto]).
    assert (HwfE1cl : wf_term (ctx_to_rules c ++ l) [] (var_to_con e1) (sort_var_to_con t)) by
      (rewrite ctx_to_rules_coincide, var_to_con_is_vtr, sort_var_to_con_is_svtr;
       apply ClosedCore.wf_term_vtr; first [assumption | typeclasses eauto]).
    assert (HwfE2cl : wf_term (ctx_to_rules c ++ l) [] (var_to_con e2) (sort_var_to_con t)) by
      (rewrite ctx_to_rules_coincide, var_to_con_is_vtr, sort_var_to_con_is_svtr;
       apply ClosedCore.wf_term_vtr; first [assumption | typeclasses eauto]).
    pose proof (rename_lang_correct _ (init_renaming_ok string) HrL) as (Hr1ok & _).
    pose proof (rename_term_correct _ Hr1ok HrE1) as (Hr2ok & _).
    pose proof (rename_term_correct _ Hr2ok HrE2) as (Hr3ok & _).
    (* Forward wf of the positive outputs + bound/unrename facts at [r7]. *)
    pose proof (@rename_egraph_bridge string _ _ _
                  (ctx_to_rules c ++ l) (var_to_con e1) (var_to_con e2) (sort_var_to_con t)
                  _ r1 r2 r3 r3 r7 Lp E1p E2p Tp
                  HwfLcl HwfE1cl HwfE2cl (init_renaming_ok string) HrL HrE1 HrE2
                  Hr3ok (rename_grows_refl r3) HrT) as Hbridge.
    destruct Hbridge as (HwfLp & HwfE1p & HwfE2p & Hr7ok & Hbl & Hbe1 & Hbe2 & Hbt
                         & HuL & HuE1 & HuE2 & HuT).
    (* The reverse lift: unrename (positive->string) then [eq_rtv] (closed->open). *)
    assert (Hrev : eq_term Lp [] Tp E1p E2p -> eq_term l c t e1 e2) by
      (rewrite ctx_to_rules_coincide in HuL;
       rewrite var_to_con_is_vtr in HuE1;
       rewrite var_to_con_is_vtr in HuE2;
       rewrite sort_var_to_con_is_svtr in HuT;
       intro Heq;
       exact (@reverse_eq_term_lift string _ _ _ l c t e1 e2 r7 Lp Tp E1p E2p
                Hwf Hwfc Hdisj He1 He2 Hr7ok Hbl Hbt Hbe1 Hbe2 HwfLp HuL HuE1 HuE2 HuT Heq)).
    exists Lp, E1p, E2p, Tp,
           [(10%nat, rsR); (1%nat, rsRR)], injp.
    split; [exact HwfLp |].
    split; [exact HwfE1p |].
    split; [exact HwfE2p |].
    split.
    { (* schedule_sound: discharge via msr_of_build_rule_set +
         rs_saturation_const_conjunct + compiled_rules_run1iter_rule_hyps.
         The two trie H9/H10 goals (intersection_keys length / map.get) are left
         as admit, gated on the separate trie-lawfulness work. *)
      (* Build Hsof (freshness) *)
      assert (Hsof : fresh PosListMap.sort_of Lp).
      { change PosListMap.sort_of with xH.
        replace Lp with (fst (rename_lang (ctx_to_rules c ++ l)
          {| p_to_v := map.empty; v_to_p := []; next_id := xO xH |}))
          by (rewrite HrL; reflexivity).
        apply rename_lang_fresh_xH; [typeclasses eauto | exact (reserved_init string)]. }
      (* Extract rename_grows chains from the two rename_term steps *)
      pose proof (rename_term_correct _ Hr1ok HrE1) as (_ & Hgrows12 & _).
      pose proof (rename_term_correct _ Hr2ok HrE2) as (_ & Hgrows23 & _).
      pose proof (rename_grows_trans Hgrows12 Hgrows23) as Hgrows13.
      (* Extract renaming_ok r4 and grows r3 r4 from rename_lang posR step *)
      pose proof (rename_lang_correct _ Hr3ok HrPR) as (Hr4ok & Hgrows34 & _).
      pose proof (rename_grows_trans Hgrows13 Hgrows34) as Hgrows14.
      (* Unfold build_rule_set to expose full_pos_trie_map *)
      unfold PositiveInstantiation.build_rule_set in Hbrs1, Hbrs2.
      (* incl posR Lp via rename_lang_filter_incl *)
      assert (Hincl_R : incl posR Lp).
      { exact (@rename_lang_filter_incl string _ _ _
                 (ctx_to_rules c) l lf
                 {| p_to_v := map.empty; v_to_p := []; next_id := xO xH |}
                 r1 r3 r4 Lp posR (init_renaming_ok string) HrL Hgrows13 Hr3ok HrPR). }
      (* forall (n,r') in posRR, exists r0 in Lp, r' = rev_rule r0 *)
      assert (Hrev_RR : forall n r', In (n, r') posRR ->
                exists r0, In (n, r0) Lp /\ r' = PositiveInstantiation.rev_rule r0).
      { exact (@AdapterGlue.rename_lang_rev_filter_recovers string _ _ _
                 (ctx_to_rules c) l (fun p => reversible p && lf p)
                 (@AdapterGlue.ctx_to_rules_rev_id string c)
                 {| p_to_v := map.empty; v_to_p := []; next_id := xO xH |}
                 r1 r4 r5 Lp posRR
                 (init_renaming_ok string) HrL Hgrows14 Hr4ok HrPRR). }
      (* Get seqsR and HmsrR *)
      destruct (@AdapterGlue.msr_of_build_rule_set
                  positive positive_Eqb positive_Eqb_ok positive_default
                  TrieMap.trie_map TrieMap.ptree_map_plus (fun A => @TrieMapFold.trie_map_ok A)
                  (@FullPosTrie.full_pos_trie_map) (fun A => @FullPosTrie.full_pos_trie_map_ok A)
                  Pos.succ Pos.leb PosListMap.sort_of Pos.lt pos_lt_asym Pos.lt_succ_diag_r Pos.lt_trans
                  Lp HwfLp Hsof rebuild_fuel posR rsR Hincl_R Hbrs1)
        as (seqsR & HrsR_eq & HmsrR).
      (* Get seqsRR and HmsrRR *)
      destruct (@AdapterGlue.msr_of_build_rule_set_rev
                  positive positive_Eqb positive_Eqb_ok positive_default
                  TrieMap.trie_map TrieMap.ptree_map_plus (fun A => @TrieMapFold.trie_map_ok A)
                  (@FullPosTrie.full_pos_trie_map) (fun A => @FullPosTrie.full_pos_trie_map_ok A)
                  Pos.succ Pos.leb PosListMap.sort_of Pos.lt pos_lt_asym Pos.lt_succ_diag_r Pos.lt_trans
                  Lp HwfLp Hsof rebuild_fuel posRR rsRR Hrev_RR Hbrs2)
        as (seqsRR & HrsRR_eq & HmsrRR).
      (* Now prove schedule_sound *)
      unfold schedule_sound.
      split.
      - (* fresh PosListMap.sort_of Lp -- already in Hsof *)
        exact Hsof.
      - (* schedule_sound_real: for each (n,rs) in [(10,rsR);(1,rsRR)], rs_saturation_hyps rs *)
        intros n rs Hin_sched.
        cbn in Hin_sched.
        pose proof (@Theorems.lang_model_ok positive positive_Eqb positive_Eqb_ok
                      PosListMap.sort_of Lp Hsof HwfLp) as Hmok.
        destruct Hin_sched as [E | HIn'].
        { (* n=10, rs=rsR *)
          injection E as Hn Hrs. rewrite <- Hrs.
          rewrite HrsR_eq.
          unfold SchedSat.rs_saturation_hyps.
          split.
          - (* const conjunct *)
            intros e i Hok Hsnd.
            exact (@QueryOptSound.rs_saturation_const_conjunct
                     positive positive_Eqb positive_Eqb_ok Pos.lt Pos.succ positive_default Pos.leb
                     positive positive_Eqb positive_Eqb_ok
                     TrieMap.trie_map (fun A => @TrieMapFold.trie_map_ok A) TrieMap.ptree_map_plus
                     TrieMap.trie_map (fun A => @TrieMapFold.trie_map_ok A)
                     (@FullPosTrie.full_pos_trie_map) (fun A => @FullPosTrie.full_pos_trie_map_ok A)
                     (option positive) (@Defs.size positive)
                     (Theorems.lang_model positive PosListMap.sort_of Lp)
                     Hmok pos_lt_asym Pos.lt_succ_diag_r Pos.lt_trans
                     rebuild_fuel seqsR HmsrR i e Hok Hsnd).
          - (* per-rule conjunct *)
            intros w e er Hin_er.
            apply (@QueryOptSound.compiled_rules_run1iter_rule_hyps
                     positive positive_Eqb positive_Eqb_ok Pos.lt Pos.succ positive_default Pos.leb
                     positive positive_Eqb positive_Eqb_ok
                     TrieMap.trie_map (fun A => @TrieMapFold.trie_map_ok A) TrieMap.ptree_map_plus
                     TrieMap.trie_map TrieMap.ptree_map_plus
                     (fun A => @TrieMapFold.trie_map_ok A)
                     (@FullPosTrie.full_pos_trie_map)
                     pos_lt_asym Pos.lt_succ_diag_r Pos.lt_trans
                     TrieMap.ptree_map_plus_ok
                     (@fpt_spaced_intersect)
                     (option positive) (@Defs.size positive)
                     w
                     (Theorems.lang_model positive PosListMap.sort_of Lp)
                     Hmok rebuild_fuel seqsR er e HmsrR Hin_er).
            + exact (QcAlignment.trie_join_H9_sn rebuild_fuel seqsR er Hin_er e w).
            + exact (QcAlignment.trie_join_H10_sn rebuild_fuel seqsR er Hin_er e w).
        }
        destruct HIn' as [E | HEmpty].
        { (* n=1, rs=rsRR *)
          injection E as Hn Hrs. rewrite <- Hrs.
          rewrite HrsRR_eq.
          unfold SchedSat.rs_saturation_hyps.
          split.
          - (* const conjunct *)
            intros e i Hok Hsnd.
            exact (@QueryOptSound.rs_saturation_const_conjunct
                     positive positive_Eqb positive_Eqb_ok Pos.lt Pos.succ positive_default Pos.leb
                     positive positive_Eqb positive_Eqb_ok
                     TrieMap.trie_map (fun A => @TrieMapFold.trie_map_ok A) TrieMap.ptree_map_plus
                     TrieMap.trie_map (fun A => @TrieMapFold.trie_map_ok A)
                     (@FullPosTrie.full_pos_trie_map) (fun A => @FullPosTrie.full_pos_trie_map_ok A)
                     (option positive) (@Defs.size positive)
                     (Theorems.lang_model positive PosListMap.sort_of Lp)
                     Hmok pos_lt_asym Pos.lt_succ_diag_r Pos.lt_trans
                     rebuild_fuel seqsRR HmsrRR i e Hok Hsnd).
          - (* per-rule conjunct *)
            intros w e er Hin_er.
            apply (@QueryOptSound.compiled_rules_run1iter_rule_hyps
                     positive positive_Eqb positive_Eqb_ok Pos.lt Pos.succ positive_default Pos.leb
                     positive positive_Eqb positive_Eqb_ok
                     TrieMap.trie_map (fun A => @TrieMapFold.trie_map_ok A) TrieMap.ptree_map_plus
                     TrieMap.trie_map TrieMap.ptree_map_plus
                     (fun A => @TrieMapFold.trie_map_ok A)
                     (@FullPosTrie.full_pos_trie_map)
                     pos_lt_asym Pos.lt_succ_diag_r Pos.lt_trans
                     TrieMap.ptree_map_plus_ok
                     (@fpt_spaced_intersect)
                     (option positive) (@Defs.size positive)
                     w
                     (Theorems.lang_model positive PosListMap.sort_of Lp)
                     Hmok rebuild_fuel seqsRR er e HmsrRR Hin_er).
            + exact (QcAlignment.trie_join_H9_sn rebuild_fuel seqsRR er Hin_er e w).
            + exact (QcAlignment.trie_join_H10_sn rebuild_fuel seqsRR er Hin_er e w).
        }
        destruct HEmpty.
    }
    split; [| exact Hrev].
    (* Is_Success carry-over: the egraph result is [Success tt]. *)
    revert Hsucc;
      generalize (egraph_reducing_equal Lp
        [(10%nat, rsR); (1%nat, rsRR)] injp
        rebuild_fuel sat_fuel efuel red_fuel E1p E2p);
      intros res Hsucc; destruct res as [u|]; [destruct u; reflexivity | destruct Hsucc].
  Qed.

End ReducingSkeleton.

(* [Is_Success] of [egraph_reducing_equal'] implies the ctx/lang disjointness
   side condition, since [egraph_reducing_equal'] fails outright when it does
   not hold.  This lets [egraph_sound] drop the disjointness premise. *)
Lemma egraph_reducing_equal'_Is_Success_disjoint
  {V} {V_Eqb : Eqb V} {V_Eqb_ok : Eqb_ok V_Eqb} {X} `{analysis V V X}
  (l : lang V)
  (lang_filter reversible : V * rule V -> bool)
  inj_rules rn n efuel red_fuel c (e1 e2 : Term.term V)
  : Is_Success (fst (egraph_reducing_equal' l lang_filter reversible inj_rules
                       rn n efuel red_fuel c e1 e2)) ->
    all (fun x => fresh x l) (map fst c).
Proof.
  unfold egraph_reducing_equal'.
  destruct (forallb (fun x => freshb x l) (map fst c)) eqn:Hg.
  2:{ cbn [fst Is_Success]; intro Hf; destruct Hf. }
  intros _.
  assert (Hall : all (fun x => Is_true (freshb x l)) (map fst c)).
  { apply Is_true_forallb. rewrite Hg. exact I. }
  revert Hall; apply all_wkn.
  intros x _ Hx.
  apply use_compute_fresh.
  exact Hx.
Qed.

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
    Is_Success (fst (egraph_reducing_equal' l filter reversible inj_rules rebuild_fuel sat_fuel efuel red_fuel c e1 e2)) ->
    eq_term l c t e1 e2.
Proof.
  intros Hl Hc He1 He2 Hsucc.
  (* The ctx/lang disjointness side condition is no longer a premise: it is
     guaranteed by [Is_Success], since [egraph_reducing_equal'] fails when the
     context variables clash with the language symbols. *)
  pose proof (egraph_reducing_equal'_Is_Success_disjoint
                l filter reversible inj_rules
                rebuild_fuel sat_fuel efuel red_fuel c e1 e2 Hsucc) as Hdisj.
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
    [prove_by_lang_db| | | | flagged_exact I].


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
  add_ctx (V:= string) (V_map := string_trie_map) string_succ "@sort_of" l (H:=weighted_size_analysis weight) true.

Definition add_open_term weight l :=
  add_open_term (V:= string) (V_map := string_trie_map) string_succ "@sort_of" l (H:=weighted_size_analysis weight) true.

Definition add_open_sort weight l :=
  add_open_sort (V:= string) (V_map := string_trie_map) string_succ "@sort_of" l (H:=weighted_size_analysis weight) true.

Definition rebuild weight fuel : state instance _ := (rebuild (idx:=string) fuel (symbol:=string) (H:=weighted_size_analysis weight)).

Notation extract_weighted := (extract_weighted (V:=string) (V_map:=string_trie_map) (V_trie:=string_list_trie_map)).
