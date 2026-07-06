Set Implicit Arguments.

(* ==========================================================================
   PROTOTYPE: generalized [inj_rules] for the REDUCTION engine (cause 3).

   Two distinct injectivity consumers exist in the codebase:

     (1) the ELABORATION engine (TypeInference): fed [sequent]s built by
         [InjRuleGen.build_general_injection_rules] from [gen_fundep_schemas].
         This one is already wired up (infer_compiler_simple_autoinj).

     (2) the REDUCTION engine ([Automation.by_reduction] ->
         [Defs.egraph_reducing_cong] -> [Defs.cong_subgoals] ->
         [Defs.select_inj_args]): fed a flat [inj_rules : list (string * list
         string)].  [by_reduction] currently passes [empty_inj_rules] (the
         literal TODO at Automation.v:561), so this path is DEAD.

   This file prototypes the (2) side: it (a) reimplements the reduction-engine
   decomposition faithfully at the string level so we can Compute on it, (b)
   generalizes it from a single injective-arg list per operator to a LIST of
   functional-dependency alternatives per operator (so [conc] gets BOTH its
   left- and right-cancellation schemas, which a single list cannot express),
   and (c) closes cause-3 wiring by GENERATING those alternatives from the
   language via the existing [gen_fundep_schemas] search -- no operator is
   named or special-cased.

   No proofs here.  We only run [vm_compute] to check the pipeline produces the
   right decompositions on the actual problem goals.

   -----------------------------------------------------------------------
   Soundness/completeness note (why the format is what it is):

   [cong_subgoals] replaces a goal [f s1 = f s2] with subgoals [s1_j = s2_j]
   for the "recursed" positions, REQUIRING every non-recursed position to be
   syntactically equal.  The replacement is SOUND by congruence regardless of
   injectivity (equal args => equal applications).  Injectivity is only needed
   for COMPLETENESS: decomposing is lossless iff [f] really is injective at the
   recursed positions given the others fixed.  A spurious schema can only make
   a proof fail, never prove a falsehood -- exactly the InjRuleGen contract.

   Hence for the reduction engine a schema is fully described by its set of
   recursed (conclusion) positions; the "shared" premise of a
   [gen_fundep_schemas] entry is automatically subsumed, because ALL
   non-recursed args are forced equal, which is >= the shared set.
   ========================================================================== *)

From coqutil Require Import Datatypes.String Map.Interface.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
From Pyrosome Require Import Tools.EGraph.Defs Tools.EGraph.TypeInference
  Tools.EGraph.InjRuleGen.
From Pyrosome Require Import Lang.LinearSubst.
Import Core.Notations.

(* Concrete string-level types (avoid shadowing library [named_list]/[ctx]). *)
Local Notation stterm := (Term.term string).
Local Notation sctx := (list (string * Term.sort string)).
Local Notation slang := (list (string * Rule.rule string)).

(* ==========================================================================
   Part A. Reduction-engine decomposition, string level.

   [select_recurse] is a faithful copy of [Defs.select_inj_args]: walk the
   constructor's context together with the two argument lists; for a position
   whose name is in [recurse], emit an [(e1,e2)] subgoal; for any other
   position require the two arguments to be syntactically equal, else fail
   ([None]).  [None] = "this schema does not apply / cannot decompose".
   ========================================================================== *)

Fixpoint select_recurse (c : sctx) (recurse : list string) (s1 s2 : list stterm)
  : option (list (stterm * stterm)) :=
  match recurse, c, s1, s2 with
  | [], [], _, _ => Some []
  | [], (_::_), _, _ => if eqb s1 s2 then Some [] else None
  | x::recurse', (x',_)::c', e1::s1', e2::s2' =>
      if eqb x x' then
        match select_recurse c' recurse' s1' s2' with
        | Some rest => Some ((e1,e2)::rest)
        | None => None
        end
      else if eqb e1 e2 then select_recurse c' recurse s1' s2'
           else None
  | _, _, _, _ => None
  end.

(* GENERALIZED schema table: per operator, a LIST of alternative recursed-arg
   sets (each is one functional dependency's conclusion positions).  A single
   [list string] (the old format) is the length-1 special case. *)
Definition gen_inj_rules := list (string * list (list string)).

(* Try each alternative for the head constructor; take the first that applies.
   Falls back to the undecomposed goal [(e1,e2)] (matching [cong_subgoals]). *)
Definition cong_subgoals_gen (l : slang) (rules : gen_inj_rules)
  (goal : stterm * stterm) : list (stterm * stterm) :=
  let '(e1,e2) := goal in
  match e1, e2 with
  | con n1 s1, con n2 s2 =>
      if eqb n1 n2 then
        match named_list_lookup_err rules n1, named_list_lookup_err l n1 with
        | Some alts, Some (term_rule c _ _) =>
            let fix try_alts alts :=
              match alts with
              | [] => [(e1,e2)]
              | recurse :: alts' =>
                  match select_recurse c recurse s1 s2 with
                  | Some sub => sub
                  | None => try_alts alts'
                  end
              end in
            try_alts alts
        | _, _ => [(e1,e2)]
        end
      else [(e1,e2)]
  | _, _ => [(e1,e2)]
  end.

(* ==========================================================================
   Part B. Generate the reduction-engine table from the language.

   [gen_fundep_schemas X L : list (string * (list string * list string))]
   already runs the counterexample search and returns (name,(shared,concl))
   dependencies -- injectivity ([shared=[]]) AND cancellation ([shared<>[]]).
   For the reduction engine we keep only the [concl] set and group by name.
   ========================================================================== *)

Fixpoint group_concls (fds : list (string * (list string * list string)))
  : gen_inj_rules :=
  match fds with
  | [] => []
  | (n,(_shared,concl)) :: rest =>
      (* drop empty conclusions: they carry no decomposition *)
      let g := group_concls rest in
      match concl with
      | [] => g
      | _ =>
          let fix ins g :=
            match g with
            | [] => [(n,[concl])]
            | (n',alts)::g' =>
                if eqb n n'
                then (n', if existsb (eqb concl) alts
                          then alts else alts ++ [concl]) :: g'
                else (n',alts) :: ins g'
            end in
          ins g
      end
  end.

Definition gen_reduce_inj_rules (X : nat) (L : slang) : gen_inj_rules :=
  group_concls (gen_fundep_schemas X L).

(* The concrete target language for the linear-CPS reduction obligations'
   substitution calculus. *)
Definition lin_target : slang := linear_block_subst ++ linear_value_subst.

(* ==========================================================================
   Part C. Computations / tests.
   ========================================================================== *)

(* --- C0. what does the constructor context look like?  (sanity) --- *)
Definition conc_ctx  := option_map (@get_ctx string) (named_list_lookup_err lin_target "conc").
Definition blksub_ctx := option_map (@get_ctx string) (named_list_lookup_err lin_target "blk_subst").

(* --- C1. the raw functional-dependency search (injectivity + cancellation) --- *)
Definition fundeps3 := Eval vm_compute in gen_fundep_schemas 3 lin_target.

(* --- C2. the reduction-engine table derived from it --- *)
Definition reduce_rules3 := Eval vm_compute in gen_reduce_inj_rules 3 lin_target.

(* pull out the two operators we care about for readability *)
Definition conc_alts := Eval vm_compute in named_list_lookup_err reduce_rules3 "conc".
Definition blksub_alts := Eval vm_compute in named_list_lookup_err reduce_rules3 "blk_subst".
Definition valsub_alts := Eval vm_compute in named_list_lookup_err reduce_rules3 "val_subst".

(* --- C3. the money shot: decompose the actual problem goals --- *)

(* (a) metavariable-substitution cancellation, the Imp.v:432 pattern:
       blk_subst g e = blk_subst g' e   (subject [e] a shared metavariable)
   should decompose to just  g = g'  (NOT stay as the whole goal). *)
Definition goal_blksub_metavar : stterm * stterm :=
  ({{e #"blk_subst" "g"  "e" }}, {{e #"blk_subst" "g'" "e" }}).

Definition test_blksub_metavar :=
  Eval vm_compute in cong_subgoals_gen lin_target reduce_rules3 goal_blksub_metavar.

(* (b) left cancellation of conc:  conc G H1 = conc G H2  ~>  H1 = H2 *)
Definition goal_conc_left : stterm * stterm :=
  ({{e #"conc" "G" "H1" }}, {{e #"conc" "G" "H2" }}).

Definition test_conc_left :=
  Eval vm_compute in cong_subgoals_gen lin_target reduce_rules3 goal_conc_left.

(* (c) right cancellation of conc:  conc G1 H = conc G2 H  ~>  G1 = G2
   This is the case a SINGLE injective-arg list cannot handle: it needs a
   different alternative than (b).  With the generalized table both fire. *)
Definition goal_conc_right : stterm * stterm :=
  ({{e #"conc" "G1" "H" }}, {{e #"conc" "G2" "H" }}).

Definition test_conc_right :=
  Eval vm_compute in cong_subgoals_gen lin_target reduce_rules3 goal_conc_right.

(* (d) negative control: genuinely-different conc, nothing shared.  The theory
   proves some such equal via associativity, so decomposing would be UNSOUND
   to accept blindly; [select_recurse] must decline (return the whole goal). *)
Definition goal_conc_bad : stterm * stterm :=
  ({{e #"conc" (#"conc" "A" "B") "C" }}, {{e #"conc" "A" (#"conc" "B" "C") }}).

Definition test_conc_bad :=
  Eval vm_compute in cong_subgoals_gen lin_target reduce_rules3 goal_conc_bad.

(* Print everything so a plain [make] of this file shows the results. *)
Set Printing Width 120.
Print conc_ctx.
Print blksub_ctx.
Print fundeps3.
Print reduce_rules3.
Print conc_alts.
Print blksub_alts.
Print valsub_alts.
Print test_blksub_metavar.
Print test_conc_left.
Print test_conc_right.
Print test_conc_bad.
