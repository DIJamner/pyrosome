(* Prototype: BETTER SEEDING for the injectivity counterexample search.

   Current seed: one generic instance per rule -> two pairs sharing a first
   component never coexist, so .1 (pair a b) = .1 (pair a c) = a never forms and
   projections are wrongly reported injective at any fuel.

   Better seed: for each equation, seed a BASE instance plus, for each context
   position i, a VARIANT that shares every generator with the base except at i.
   Two applications that differ only in a dropped argument then land in the same
   e-class, and the scan refutes that position -- no operator special-casing. *)
From coqutil Require Import Datatypes.String Map.Interface Datatypes.Result.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string. Open Scope list.
From Utils Require Import Utils Monad.
From Pyrosome Require Import Theory.Core Tools.EGraph.Defs Tools.EGraph.InjRuleGen
  Tools.EGraph.TypeInference Tools.PosRenaming.
From Utils.EGraph Require Import Semantics.
From Utils Require Import TrieMap PosListMap FullPosTrie.
From Pyrosome.Lang Require Import SimpleVCC SimpleVCPS SimpleUnit PolySubst.
Import PArith StateMonad.
Import Core.Notations.

Local Notation slang := (list (string * Rule.rule string)).
Definition cover : slang :=
  cc_lang ++ prod_cc ++ cps_prod_lang ++ unit_lang ++ block_subst ++ value_subst.

Section Better.
  Local Open Scope positive.
  Local Notation instance := (Defs.instance positive positive trie_map trie_map
                                (@FullPosTrie.full_pos_trie_map) (option positive)).
  Local Notation poslang := (@Rule.lang positive).
  Notation weight := InjRuleGen.triv_weight.

  Definition seed_open (l : poslang) (sub : list (positive*positive))
    (e : Term.term positive) : state instance _ :=
    InjRuleGen.add_open_term weight l false sub e.

  (* offset for fresh duplicate variable names (larger than any real name) *)
  Definition BIG : positive := 1000000.

  (* c extended with a same-sort duplicate of each var (dup names = orig+BIG;
     dup sorts still reference the ORIGINAL names, so add_ctx gives each dup a
     generator of the SAME sort as its original). *)
  Definition dup_ctx (c : Term.ctx positive) : Term.ctx positive :=
    c ++ map (fun '(p,t) => ((p + BIG)%positive, t)) c.

  (* seed both sides under the base sub + one variant per position, where the
     variant remaps exactly one var to its (same-sort) duplicate generator. *)
  Definition seed_eq (l : poslang) (c : Term.ctx positive) (e1 e2 : Term.term positive)
    : state instance unit :=
    @! let subA <- InjRuleGen.add_ctx weight l (dup_ctx c) in
       let _ <- seed_open l subA e1 in
       let _ <- seed_open l subA e2 in
       let _ <- list_Miter (fun '(pi,_) =>
                  let gdup := named_list_lookup default subA (pi + BIG)%positive in
                  let subi := map (fun '(k,v) =>
                                if Pos.eqb k pi then (k, gdup) else (k,v)) subA in
                  @! let _ <- seed_open l subi e1 in
                     let _ <- seed_open l subi e2 in
                     ret tt)
                  c in
       ret tt.

  Definition seed_rule2 (l : poslang) (nr : positive * Rule.rule positive)
    : state instance unit :=
    let '(n,r) := nr in
    match r with
    | term_eq_rule c e1 e2 _ => seed_eq l c e1 e2
    | term_rule c _ _ =>
        @! let sub <- InjRuleGen.add_ctx weight l c in
           let _ <- seed_open l sub (con n (id_args c)) in ret tt
    | _ => Mret tt  (* sort rules irrelevant to term-op injectivity here *)
    end.

  Definition run_eq2 (fuel : nat) (l : poslang) : instance :=
    snd ((@! let _ <- list_Miter (seed_rule2 l) l in
             let _ <- InjRuleGen.saturate_gen weight fuel (InjRuleGen.eq_seqs l) in
             ret tt) InjRuleGen.empty_egraph).

End Better.

Definition gen2 (X : nat) (L : slang) : list (string * (list string * list string)) :=
  let '(lp, rn) := rename_lang L init_renaming in
  InjRuleGen.fundep_schemas_of (run_eq2 X lp) rn L.

Definition selof (fds : list (string * (list string * list string))) :=
  filter (fun p => existsb (String.eqb (fst p)) [".1"; ".2"; "pair"; "closure"; "cmp"; "snoc"]) fds.

Set Printing Width 140.
(* RESULT (vs stock single-instance seeding, which reports .1/.2 fully injective
   at any fuel): the base+variant seeding refutes the projections' value arg --
   .1/.2 : (["v"], ["B";"A";"G"])  (v NOT determined) -- while snoc stays fully
   injective and pair/cmp/closure gain sound cancellations.  No special-casing. *)
Definition g4 := Eval vm_compute in selof (gen2 4 cover). Print g4.
