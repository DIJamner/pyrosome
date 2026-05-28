(* Debug scaffolding: bounded diagnosis of "why don't these two terms unify?".

   The dominant failure mode of the e-graph automation is non-termination
   *caused by* a failed unification: the saturation loop short-circuits the
   moment the two subject ids x1/x2 merge (the are_unified/weight-decrease
   predicate in egraph_reducing_equal_step); when they never merge it runs to
   fuel exhaustion while the graph explodes.

   This file runs a *bounded* replica of the real loop (egraph_reducing_equal'
   -> egraph_reducing_equal -> egraph_reducing_cong) so that it always returns,
   and reports -- keyed to the two subject ids -- whether they unified, their
   extracted normal forms, the structural point where they diverge
   (cong_subgoals, the very decomposition the real engine recurses into), and
   per-iteration size stats.  Everything is rendered back to readable source
   terms through the renaming.

   The setup (renaming + rule-set construction) is copied verbatim from the
   rename_and_run block of egraph_reducing_equal' (Pyrosome/Tools/EGraph/Defs.v)
   so the diagnosis runs on exactly the inputs the real automation would. *)
Set Implicit Arguments.

From Stdlib Require Import Lists.List Strings.String BinNums BinPos.
Import ListNotations.
Open Scope string.
Open Scope list.

From coqutil Require Import Map.Interface Datatypes.Result.
From Utils Require Import Utils Monad UnionFind TrieMap NamedList Result.
From Utils.EGraph Require Import Defs.
Import Monad.StateMonad.
From Pyrosome.Theory Require Import Core.
Import Core.Notations.
From Pyrosome.Tools Require Import PosRenaming.
From Pyrosome.Tools.EGraph Require Import Defs.
From Pyrosome.Tools.EGraph.Debug Require Import Observe.
Import PosListMap.
Import PositiveInstantiation.

(* Make run_query's bookkeeping arguments implicit, mirroring Test.v, so we can
   call it as `run_query rs n g` at the positive instantiation. *)
Arguments Utils.EGraph.Defs.run_query {idx}%_type_scope {Eqb_idx} {symbol}%_type_scope
  {symbol_map}%_function_scope {symbol_map_plus} {idx_map}%_function_scope {idx_map_plus}
  {idx_trie}%_function_scope {analysis_result}%_type_scope
  spaced_list_intersect%_function_scope rs n%_nat_scope _.
Notation run_query := (Utils.EGraph.Defs.run_query (@PosListMap.compat_intersect)).

(* The forward/reverse rule schedule the engine runs on. *)
Notation schedule := (list (nat * rule_set positive positive trie_map trie_map)).

Section WithSrc.
  Context {V : Type} {V_Eqb : Eqb V} {V_default : WithDefault V}.

  Notation named_list := (@named_list V).
  Notation named_map := (@named_map V).
  Notation term := (@term V).
  Notation ctx := (@ctx V).
  Notation sort := (@sort V).
  Notation rule := (@rule V).
  Notation lang := (@lang V).

  (* ---- (a) expose the renamed inputs -------------------------------------
     A copy of the rename_and_run block of egraph_reducing_equal' that stops
     before calling the inner loop and instead returns the renamed inputs
     (l', schedule, e1', e2', inj) together with the final renaming. *)
  Definition egraph_reducing_setup
      (l : lang) (lang_filter reversible : V * rule -> bool)
      (inj_rules : list (V * list V)) (rn : nat) (c : ctx) (e1 e2 : term)
    : (Rule.lang positive * schedule * Term.term positive * Term.term positive
       * list (positive * list positive)) * renaming V :=
    let rename_and_run : state (renaming V) _ :=
      @! let l' <- rename_lang (ctx_to_rules c ++ l) in
         let e1' <- rename_term (var_to_con e1) in
         let e2' <- rename_term (var_to_con e2) in
         let {state (renaming V)} pos_rules <-
           rename_lang (ctx_to_rules c ++ filter lang_filter l) in
         let rev_rules := named_map rev_rule
                            (filter (fun p => andb (reversible p) (lang_filter p)) l) in
         let {state (renaming V)} pos_rev_rules <-
           rename_lang (ctx_to_rules c ++ rev_rules) in
         let renamed_inj_rules <- list_Mmap rename_inj inj_rules in
         ret {state (renaming V)}
           (l',
            [(10%nat, build_rule_set rn pos_rules l');
             (1%nat,  build_rule_set rn pos_rev_rules l')],
            e1', e2', renamed_inj_rules)
    in
    rename_and_run {| p_to_v := map.empty; v_to_p := []; next_id := 2 |}.

  (* The long_horizon egraph_reducing_equal' now guards on this: every context
     variable must be fresh for the language, else [ctx_to_rules c ++ l] is not
     all_fresh and the reduction would be unsound -- the real function returns
     an error instead of running.  The diagnosis surfaces the same condition. *)
  Definition ctx_lang_disjoint (l : lang) (c : ctx) : bool :=
    forallb (fun x => freshb x l) (map fst c).

  (* Cap every per-schedule-entry fuel at k, so a single bounded run can never
     blow up inside saturate_until even with the engine's default weights. *)
  Definition cap_schedule (k : nat) (s : schedule) : schedule :=
    map (fun p => (Nat.min k (fst p), snd p)) s.

  (* ---- (b) bounded stepping keyed to x1/x2 ------------------------------- *)
  Definition run_step (l' : Rule.lang positive) (s : schedule)
      (rfuel n : nat) (e1' e2' : Term.term positive) :=
    egraph_reducing_equal_step ptree_map_plus (@pos_trie_map) Pos.succ sort_of
      (@compat_intersect) l' s rfuel n e1' e2'.

  Definition nf_pos (g : instance) (efuel : nat) (x : positive) : Term.term positive :=
    match Defs.extract_weighted g efuel x with
    | Success t => t
    | Failure _ => var x
    end.

  (* The new egraph_reducing_cong distinguishes three per-step outcomes
     (see the long_horizon Defs.v):
       it_res=true,  it_unified=true   -> Solved (ids merged in the egraph)
       it_res=true,  it_unified=false  -> Simplified (weight decreased; the
                                          real loop recurses on the extracted
                                          simpler forms)
       it_res=false                    -> Stuck: saturation ran to completion
                                          without converging.  This is the
                                          fuel-exhaustion leaf where the real
                                          function now returns Failure instead
                                          of recursing -- i.e. the genuine
                                          "these two never unify" diagnosis. *)
  Record iter_report :=
    {
      it_fuel : nat;           (* outer saturation fuel used for this run *)
      it_res : bool;           (* step's termination flag (unified OR simpler) *)
      it_unified : bool;       (* did the two subject ids actually merge? *)
      it_nf1 : term;           (* extracted normal form of side 1 (readable) *)
      it_nf2 : term;
      it_diverge : list (term * term); (* structural decomposition of (nf1,nf2) *)
      it_stats : egraph_stats (V:=V);
    }.

  (* Classify a finished step the way the real egraph_reducing_cong does. *)
  Definition step_outcome (res unified : bool) : string :=
    if res then (if unified then "solved" else "simplified")
    else "stuck (saturated, no convergence)".

  (* One bounded run at outer fuel n, for a positive-level goal (e1',e2'). *)
  Definition report_at (r : renaming V) (l' : Rule.lang positive) (s : schedule)
      (inj : list (positive * list positive)) (rfuel efuel n : nat)
      (e1' e2' : Term.term positive) : iter_report :=
    let '(res, x1, x2, g) := run_step l' s rfuel n e1' e2' in
    let p1 := nf_pos g efuel x1 in
    let p2 := nf_pos g efuel x2 in
    {|
      it_fuel := n;
      it_res := res;
      it_unified := fst (are_unified x1 x2 g);
      it_nf1 := unrename_term r p1;
      it_nf2 := unrename_term r p2;
      it_diverge := map (fun pr => (unrename_term r (fst pr), unrename_term r (snd pr)))
                      (cong_subgoals l' inj (p1, p2));
      it_stats := Observe.stats r g;
    |}.

  (* Trajectory for the top-level pair: one report per outer fuel 1..maxn.
     Shows whether the gap ever closes and whether the graph is exploding. *)
  Definition diagnose_trace (l : lang) (lang_filter reversible : V * rule -> bool)
      (inj_rules : list (V * list V))
      (rn rfuel efuel maxn sched_cap : nat) (c : ctx) (e1 e2 : term)
    : result (list iter_report) :=
    if ctx_lang_disjoint l c then
      let '(sd, r) := egraph_reducing_setup l lang_filter reversible inj_rules rn c e1 e2 in
      let '(l', s, e1', e2', inj) := sd in
      let s := cap_schedule sched_cap s in
      Success (map (fun n => report_at r l' s inj rfuel efuel n e1' e2') (seq 1%nat maxn))
    else error:("egraph_diagnose: a context variable clashes with a language symbol"
                "(egraph_reducing_equal' would fail this guard before running)").

  (* ---- (c) recurse to the stuck leaf (mirrors egraph_reducing_cong) ------
     Exactly parallels the long_horizon egraph_reducing_cong control flow:
       - decompose the incoming goals with cong_subgoals at the top of each
         red-fuel level (flat_map);
       - run one bounded step per goal;
       - res=true & unified  -> Solved, stop this branch;
       - res=true & !unified -> Simplified, recurse on the EXTRACTED simpler
         forms [(p1,p2)] (the real loop does the same, not on subgoals);
       - res=false           -> Stuck (saturation completed, no convergence):
         report and stop -- this is where the real function now returns Failure
         instead of looping forever.
     Returns every leaf report rather than short-circuiting, so the whole
     reduction tree is visible. *)
  Fixpoint diagnose_cong (r : renaming V) (l' : Rule.lang positive) (s : schedule)
      (inj : list (positive * list positive)) (rfuel sat_fuel efuel depth : nat)
      (goals : list (Term.term positive * Term.term positive)) : list iter_report :=
    match depth with
    | 0%nat => []   (* red fuel exhausted: real fn returns "out of fuel for reduction" *)
    | S depth =>
        flat_map
          (fun goal =>
             let '(e1', e2') := goal in
             let '(res, x1, x2, g) := run_step l' s rfuel sat_fuel e1' e2' in
             let p1 := nf_pos g efuel x1 in
             let p2 := nf_pos g efuel x2 in
             let uni := fst (are_unified x1 x2 g) in
             let rep :=
               {| it_fuel := sat_fuel;
                  it_res := res;
                  it_unified := uni;
                  it_nf1 := unrename_term r p1;
                  it_nf2 := unrename_term r p2;
                  it_diverge := map (fun pr => (unrename_term r (fst pr),
                                                 unrename_term r (snd pr)))
                                  (cong_subgoals l' inj (p1, p2));
                  it_stats := Observe.stats r g |}
             in
             if res then
               if uni then [rep]   (* Solved *)
               else rep :: diagnose_cong r l' s inj rfuel sat_fuel efuel depth [(p1, p2)]
             else [rep])           (* Stuck: saturation fixpoint, no convergence *)
          (flat_map (cong_subgoals l' inj) goals)
    end.

  (* ---- top-level: pinpoint the stuck leaf for (e1,e2) ------------------- *)
  Definition diagnose (l : lang) (lang_filter reversible : V * rule -> bool)
      (inj_rules : list (V * list V))
      (rn rfuel sat_fuel efuel red_depth sched_cap : nat) (c : ctx) (e1 e2 : term)
    : result (list iter_report) :=
    if ctx_lang_disjoint l c then
      let '(sd, r) := egraph_reducing_setup l lang_filter reversible inj_rules rn c e1 e2 in
      let '(l', s, e1', e2', inj) := sd in
      let s := cap_schedule sched_cap s in
      Success (diagnose_cong r l' s inj rfuel sat_fuel efuel red_depth [(e1', e2')])
    else error:("egraph_diagnose: a context variable clashes with a language symbol"
                "(egraph_reducing_equal' would fail this guard before running)").

  (* ---- (d) rule probing: which rules' LHS match the (bounded) graph? ----
     Returns (rule_index, number_of_matching_assignments) for each compiled
     rule of rs.  An expected bridging rule with 0 matches => its precondition
     is absent in the saturated graph. *)
  Definition probe_rules (g : instance)
      (rs : rule_set positive positive trie_map trie_map) : list (nat * nat) :=
    map (fun n => (n, match fst (run_query rs n g) with
                      | Some asgn => List.length asgn
                      | None => 0%nat
                      end))
      (seq 0%nat (List.length rs.(compiled_rules _ _ _ _))).

  (* Run the top pair once at sat_fuel and probe the forward rule set against
     the resulting state. *)
  Definition diagnose_probe (l : lang) (lang_filter reversible : V * rule -> bool)
      (inj_rules : list (V * list V))
      (rn rfuel sat_fuel efuel sched_cap : nat) (c : ctx) (e1 e2 : term)
    : result (iter_report * list (nat * nat)) :=
    if ctx_lang_disjoint l c then
      let '(sd, r) := egraph_reducing_setup l lang_filter reversible inj_rules rn c e1 e2 in
      let '(l', s0, e1', e2', inj) := sd in
      let s := cap_schedule sched_cap s0 in
      let '(res, x1, x2, g) := run_step l' s rfuel sat_fuel e1' e2' in
      let p1 := nf_pos g efuel x1 in
      let p2 := nf_pos g efuel x2 in
      let rep :=
        {| it_fuel := sat_fuel;
           it_res := res;
           it_unified := fst (are_unified x1 x2 g);
           it_nf1 := unrename_term r p1;
           it_nf2 := unrename_term r p2;
           it_diverge := map (fun pr => (unrename_term r (fst pr),
                                          unrename_term r (snd pr)))
                           (cong_subgoals l' inj (p1, p2));
           it_stats := Observe.stats r g |}
      in
      let fwd := match s0 with (_, rs) :: _ => rs | [] => build_rule_set rn [] [] end in
      Success (rep, probe_rules g fwd)
    else error:("egraph_diagnose: a context variable clashes with a language symbol"
                "(egraph_reducing_equal' would fail this guard before running)").

End WithSrc.
