From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string. Open Scope list.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core.
From Pyrosome.Lang.OTT Require Import Pi.
Import Core.Notations.
(* The largest axiom-free prefix of ott_pi: everything but "Pi_rel eta",
   which Lang/OTT/Pi.v adds with push_rule_todo (Axiom todo). *)
Definition ott_pi_noeta : @lang string := Eval vm_compute in (tl ott_pi).
