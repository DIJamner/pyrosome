(* DiagSortOfCount.v
   End-to-end measurement: does the pattern-rigidity gate actually remove
   sort_of atoms from compiled e-graph rule queries?

   Strategy: compile each eq rule in poly_full and Ltgt via the same
   rule_to_log_rule instantiation that the production pipeline uses
   (PositiveInstantiation), then count atom_clause's whose atom_fn equals
   PosListMap.sort_of (= xH) in seq_assumptions.

   Expected (from DiagRigidity/DiagRigiditySTLC coverage numbers):
     poly_full: A = F + 4  (four Lam-eta candidates kept),  A << B
     Ltgt:      A = F exactly (100% skip rate)

   where B = old-gate baseline (every ctx var of every eq rule contributes one
   sort_of atom), F = floor (vars NOT in fv(LHS), always emit), A = actual count.
*)

Set Implicit Arguments.
From Stdlib Require Import Lists.List Strings.String BinNums NArith PArith.BinPos.
Import ListNotations.
Open Scope string. Open Scope list.

From coqutil Require Import Datatypes.String Datatypes.Result Map.Interface.
From Utils Require Import Utils Monad Result.
From Utils Require Import TrieMap FullPosTrie FullPosTrieConv TrieMapFold.
From Utils.EGraph Require Import Defs Semantics.
From Pyrosome.Theory Require Import Core Term Rule.
From Pyrosome.Tools Require Import PosRenaming.
From Pyrosome.Tools.EGraph Require Import Defs.
Import PositiveInstantiation.   (* exports PosListMap; sort_of = xH *)
Import PosListMap.              (* positive_Eqb, positive_default *)
Import Core.Notations.

From Pyrosome.Lang Require Import PolySubst PolyCompilers.
From Pyrosome.Lang Require Import SimpleVSubst SimpleVSTLC SimpleVCPS SimpleVFixCPS.

(* ================================================================== *)
(* Notation shortcuts                                                  *)
(* ================================================================== *)

(* Fully-qualified types to avoid notation ambiguity. *)
Notation pos_lang   := (@Rule.lang positive).
Notation str_lang   := (@Rule.lang string).
Notation pos_rule   := (@Rule.rule positive).
Notation str_rule   := (@Rule.rule string).
Notation pos_ctx    := (@Term.ctx positive).
Notation str_ctx    := (@Term.ctx string).
Notation pos_term   := (@Term.term positive).
Notation str_term   := (@Term.term string).
Notation pos_seq    := (@EGraph.Semantics.sequent positive positive).
Notation pos_clause := (@EGraph.Semantics.clause positive positive).

(* ================================================================== *)
(* Language definitions                                               *)
(* ================================================================== *)

Definition poly_full : str_lang :=
  poly ++ exp_param_substs ++ exp_ty_subst ++ val_param_substs ++ val_ty_subst
       ++ env_ty_subst ++ ty_subst_lang ++ exp_parameterized ++ val_parameterized
       ++ ty_env_lang.

Definition Ltgt : str_lang :=
  fix_cps_lang ++ cps_prod_lang ++ cps_lang ++ block_subst ++ value_subst.

(* ================================================================== *)
(* Helper: rename a string language to positive.                       *)
(* Uses next_id = 2 = xO xH so that sort_of = xH = 1 is reserved.    *)
(* ================================================================== *)

Definition init_r : @PosRenaming.renaming string :=
  {| PosRenaming.p_to_v := map.empty;
     PosRenaming.v_to_p := [];
     PosRenaming.next_id := xO xH |}.

Definition rename_lang_str (l : str_lang) : pos_lang :=
  fst (@PosRenaming.rename_lang string _ l init_r).

(* ================================================================== *)
(* Core helper: compile all eq rules of a positive language l' to     *)
(* their sequents.  rb_fuel = 100, same as ComputeWf/build_rule_set.  *)
(* ================================================================== *)

(* Mirrors the list_Mmap step inside rule_set_from_lang / build_rule_set
   but returns the individual sequents instead of building the rule_set.
   We pass the same 4 explicit section-var args as build_rule_set uses:
     V_map_plus = ptree_map_plus
     V_trie     = full_pos_trie_map
     succ       = Pos.succ
     sort_of    = sort_of (= xH, from PosListMap)
   analysis_result is named-arg'd to unit; unit_analysis (Utils/EGraph/Defs.v
   line 932) is found by typeclass resolution.                           *)
Definition seqs_from_lang
    (rf : nat) (l_eqn l_full : pos_lang)
    : Result.result (list pos_seq) :=
  (* rule_to_log_rule explicit args (confirmed via About):
       V_map, V_trie, succ, sort_of, l, rf, n, r.
     V implicit (positive), V_Eqb/V_default from instances,
     analysis_result inferred as unit via Utils.EGraph.Defs.unit_analysis export. *)
  list_Mmap (fun '(n,r) =>
      Pyrosome.Tools.EGraph.Defs.rule_to_log_rule
        TrieMap.trie_map
        (@FullPosTrie.full_pos_trie_map)
        Pos.succ
        sort_of
        l_full
        rf n r)
    l_eqn.

(* Convenience wrapper: compile all eq rules of l_full, using l_full as
   the context language (same as production's build_rule_set).           *)
Definition compile_all_eq_rules (l_full : pos_lang)
    : Result.result (list pos_seq) :=
  seqs_from_lang 100
    (PositiveInstantiation.filter_eqn_rules l_full)
    l_full.

(* ================================================================== *)
(* Counting helpers                                                    *)
(* ================================================================== *)

(* Count sort_of atoms in the assumptions of a single sequent. *)
Definition count_sort_of_seq (s : pos_seq) : nat :=
  List.length (List.filter (fun cl =>
    match cl with
    | @EGraph.Semantics.atom_clause _ _ a => eqb a.(atom_fn) sort_of
    | _ => false
    end) s.(seq_assumptions)).

(* Sum sort_of atoms across a list of sequents (Failure = 0). *)
Definition total_sort_of (r : Result.result (list pos_seq)) : nat :=
  match r with
  | Success seqs => fold_left (fun (acc : nat) s => Nat.add acc (count_sort_of_seq s)) seqs 0%nat
  | Failure _ => 0
  end.

(* ================================================================== *)
(* Baseline counters (string-side, before renaming)                   *)
(* ================================================================== *)

(* Count ctx vars of eq rules = "old-gate baseline" B.
   Under the old gate every ctx var of every eq rule got a sort_of atom. *)
Definition count_ctx_vars_eq (l : str_lang) : nat :=
  fold_left (fun (acc : nat) '(_, r) =>
    Nat.add acc (match r with
          | term_eq_rule c _ _ _ => List.length c
          | sort_eq_rule c _ _   => List.length c
          | _ => 0%nat
          end)) l 0%nat.

(* Count vars NOT in fv(LHS) = floor F.
   These always get a sort_of atom (the gate only skips vars in fv(LHS)
   that are additionally rigid).  For term_eq_rule fv = fv(e1),
   for sort_eq_rule fv = fv_sort(t1). *)
Definition count_outside_lhs (l : str_lang) : nat :=
  fold_left (fun (acc : nat) '(_, r) =>
    Nat.add acc (match r with
          | term_eq_rule c e1 _ _ =>
              List.length (List.filter (fun x => negb (inb x (fv e1))) (map fst c))
          | sort_eq_rule c t1 _ =>
              List.length (List.filter (fun x => negb (inb x (fv_sort t1))) (map fst c))
          | _ => 0%nat
          end)) l 0%nat.

(* ================================================================== *)
(* Pre-compute the positive languages (avoid re-evaluation)            *)
(* ================================================================== *)

Definition poly_full_pos : pos_lang :=
  Eval vm_compute in rename_lang_str poly_full.

Definition Ltgt_pos : pos_lang :=
  Eval vm_compute in rename_lang_str Ltgt.

(* ================================================================== *)
(* Per-rule breakdown: list (rule_index, sort_of_count) pairs          *)
(* with nonzero count.  Rule indices are positives (from rename).      *)
(* ================================================================== *)

Definition nonzero_rule_counts (r : Result.result (list pos_seq)) : list (nat * nat) :=
  match r with
  | Failure _ => []
  | Success seqs =>
      filter (fun '(_, c) => Nat.ltb 0%nat c)
        (List.combine (List.seq 0%nat (List.length seqs))
                      (map count_sort_of_seq seqs))
  end.

(* ================================================================== *)
(* Failure check                                                       *)
(* ================================================================== *)

Definition any_failure (r : Result.result (list pos_seq)) : bool :=
  match r with
  | Failure _ => true
  | Success _ => false
  end.

(* ================================================================== *)
(* Compile (pre-compute results to avoid re-evaluation in Evals)       *)
(* ================================================================== *)

Definition poly_compiled : Result.result (list pos_seq) :=
  Eval vm_compute in compile_all_eq_rules poly_full_pos.

Definition Ltgt_compiled : Result.result (list pos_seq) :=
  Eval vm_compute in compile_all_eq_rules Ltgt_pos.

(* ================================================================== *)
(* Eval outputs                                                        *)
(* ================================================================== *)

Eval vm_compute in ("poly_full failures?", any_failure poly_compiled).
Eval vm_compute in ("Ltgt failures?",      any_failure Ltgt_compiled).

Eval vm_compute in
  ("poly_full",
   "eq rules",                   List.length (filter_eqn_rules poly_full_pos),
   "ctx-var total (old-gate B)", count_ctx_vars_eq poly_full,
   "sort_of atoms now (A)",      total_sort_of poly_compiled,
   "floor (vars outside fv A)",  count_outside_lhs poly_full).

Eval vm_compute in
  ("Ltgt",
   "eq rules",                   List.length (filter_eqn_rules Ltgt_pos),
   "ctx-var total (old-gate B)", count_ctx_vars_eq Ltgt,
   "sort_of atoms now (A)",      total_sort_of Ltgt_compiled,
   "floor (vars outside fv A)",  count_outside_lhs Ltgt).

(* Per-rule breakdown for poly_full: (0-based seq index, sort_of count)
   for rules with nonzero sort_of atoms. *)
Eval vm_compute in
  ("poly_full nonzero sort_of counts (seq-index, count)",
   nonzero_rule_counts poly_compiled).

Eval vm_compute in
  ("Ltgt nonzero sort_of counts (seq-index, count)",
   nonzero_rule_counts Ltgt_compiled).
