(* Phase 1 prototype: the weakened checker syntactic_sort_eq_langb', and
   vm_compute certificates on the real poly + existential stacks. *)
Set Implicit Arguments.
From Stdlib Require Import Lists.List Strings.String.
Import ListNotations.
Open Scope string. Open Scope list.
From coqutil Require Import Datatypes.String.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Theory.SyntacticSorts.
From Pyrosome Require Import Lang.PolySubst Lang.PolyCompilers.
Import Core.Notations.

Notation term := (@term string).
Notation ctx := (@ctx string).
Notation sort := (@sort string).
Notation rule := (@rule string).
Notation lang := (@lang string).

(* The relaxed conjunct (3'): an index-head term_eq is OK iff it is ungated,
   i.e. every ctx variable occurs in fv(e1) ++ fv(e2). *)
Definition ungated_or_nonindex (R : list string) (r : rule) : bool :=
  match r with
  | term_eq_rule c e1 e2 t =>
      negb (inb (sort_head t) R) || inclb (map fst c) (fv e1 ++ fv e2)
  | _ => true
  end.

Definition syntactic_sort_eq_langb' (l : lang) : bool :=
  let R := index_heads_b l in
  forallb (fun p => negb (is_sort_eq_ruleb (snd p))) l
  && inclb (close_index_step l R) R
  && forallb (fun p => ungated_or_nonindex R (snd p)) l.

(* ---- the full stacks the e-graph actually queries ---- *)
Definition poly_full :=
  poly ++ exp_param_substs ++ exp_ty_subst ++ val_param_substs ++ val_ty_subst
       ++ env_ty_subst ++ ty_subst_lang ++ exp_parameterized ++ val_parameterized
       ++ ty_env_lang.

Definition exists_full :=
  exists_lang ++ poly_full.

(* Sanity: the OLD checker rejects both. *)
Eval vm_compute in (syntactic_sort_eq_langb poly_full).
Eval vm_compute in (syntactic_sort_eq_langb exists_full).
(* The NEW checker should ACCEPT both. *)
Eval vm_compute in (syntactic_sort_eq_langb' poly_full).
Eval vm_compute in (syntactic_sort_eq_langb' exists_full).

(* A GATED language must still be REJECTED by the new checker.  Mini
   language mirroring cex3: sort A,B,S,ty; val indexed by ty makes ty an
   index; a term-eq at ty gated by an unreferenced witness w:S. *)
Definition gated_lang : lang :=
  [("bad", term_eq_rule [("w", scon "S" []); ("D", scon "tyenv" [])]
              (con "a" [var "D"]) (con "b" [var "D"]) (scon "ty" [var "D"]));
   ("val", sort_rule [("D", scon "tyenv" []); ("A", scon "ty" [var "D"])] []);
   ("b", term_rule [("D", scon "tyenv" [])] [] (scon "ty" [var "D"]));
   ("a", term_rule [("D", scon "tyenv" [])] [] (scon "ty" [var "D"]));
   ("S", sort_rule [] []);
   ("ty", sort_rule [("D", scon "tyenv" [])] []);
   ("tyenv", sort_rule [] [])].

Eval vm_compute in (index_heads_b gated_lang).
Eval vm_compute in (syntactic_sort_eq_langb' gated_lang).  (* expect false: w gates *)

(* Decompose which conjunct fails on poly_full. *)
Definition Rpf := index_heads_b poly_full.
Eval vm_compute in (forallb (fun p => negb (is_sort_eq_ruleb (snd p))) poly_full). (* (1) *)
Eval vm_compute in (inclb (close_index_step poly_full Rpf) Rpf).                   (* (2) *)
Eval vm_compute in (forallb (fun p => ungated_or_nonindex Rpf (snd p)) poly_full). (* (3') *)

(* If (3') fails, list the offending (index-head, gated) term_eq rules. *)
Eval vm_compute in
  (map fst (filter (fun p => negb (ungated_or_nonindex Rpf (snd p))) poly_full)).

(* If (1) fails, list sort_eq rules. *)
Eval vm_compute in
  (map fst (filter (fun p => is_sort_eq_ruleb (snd p)) poly_full)).

(* ---- Fix (2): saturate index heads to a fixpoint instead of one-pass check ---- *)
Fixpoint saturate_heads (fuel : nat) (l : lang) (R : list string) : list string :=
  match fuel with
  | 0 => R
  | S fuel' =>
      let R' := close_index_step l R in
      if inclb R' R then R else saturate_heads fuel' l R'
  end.
Definition index_heads_sat (l : lang) : list string :=
  saturate_heads (List.length l) l (seed_index_heads l).

Definition syntactic_sort_eq_langb'' (l : lang) : bool :=
  let R := index_heads_sat l in
  forallb (fun p => negb (is_sort_eq_ruleb (snd p))) l
  && inclb (close_index_step l R) R
  && forallb (fun p => ungated_or_nonindex R (snd p)) l.

Eval vm_compute in (index_heads_sat poly_full).
Eval vm_compute in (syntactic_sort_eq_langb'' poly_full).   (* want true *)
Eval vm_compute in (syntactic_sort_eq_langb'' exists_full).  (* want true *)
(* offenders under the SATURATED index heads, if any *)
Eval vm_compute in
  (let R := index_heads_sat poly_full in
   map fst (filter (fun p => negb (ungated_or_nonindex R (snd p))) poly_full)).
Eval vm_compute in (syntactic_sort_eq_langb'' gated_lang).   (* want false *)
