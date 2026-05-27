Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm Require Import Domain EvalRel Env Determinism Model.
From Pyrosome.Lang.OTT Require Import Base Nat.
Import Core.Notations.

Definition fo_lang := ott_nat ++ ott_base ++ subst_ott ++ ott_info.

Definition term_rules_only : list (string * rule string) :=
  filter (fun r => match snd r with term_rule _ _ _ => true | _ => false end) fo_lang.
Definition term_eq_rules_only : list (string * rule string) :=
  filter (fun r => match snd r with term_eq_rule _ _ _ _ => true | _ => false end) fo_lang.
Definition sort_rules_only : list (string * rule string) :=
  filter (fun r => match snd r with sort_rule _ _ => true | _ => false end) fo_lang.
Definition sort_eq_rules_only : list (string * rule string) :=
  filter (fun r => match snd r with sort_eq_rule _ _ _ => true | _ => false end) fo_lang.

Compute (map fst term_rules_only).
Compute (map fst term_eq_rules_only).
Compute (map fst sort_rules_only).
Compute (map fst sort_eq_rules_only).
(* Print full term rules with sort info *)
Compute term_rules_only.
Compute term_eq_rules_only.
