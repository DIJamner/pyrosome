(* Phase 1 certificates against the REAL src checker: the weakened decision
   procedure [SyntacticSorts.syntactic_sort_eq_langb'] ACCEPTS the full
   polymorphic and existential language stacks and REJECTS a gated
   counterexample language (the SubstWfCounterexample3 shape).

   Once the Phase 2 transport lemma (WIP/SortTransport.v:
   [syntactic_sort_eq_langb'_transport_at]) is proven, flipping
   Tools/EGraph/Defs.v's [syntactic_sort_gate] to [syntactic_sort_eq_langb']
   and the AdapterGlue discharge to that lemma enables sort_of-free queries
   for every language certified here. *)
Set Implicit Arguments.
From Stdlib Require Import Lists.List Strings.String.
Import ListNotations.
Open Scope string. Open Scope list.
From coqutil Require Import Datatypes.String.
From Utils Require Import Utils.
From Pyrosome Require Import Theory.Core Theory.SyntacticSorts.
From Pyrosome Require Import Lang.PolySubst Lang.PolyCompilers.
Import Core.Notations.

Notation lang := (@lang string).
Notation rule := (@rule string).
Notation sort := (@sort string).

(* The full stacks the e-graph actually queries. *)
Definition poly_full : lang :=
  poly ++ exp_param_substs ++ exp_ty_subst ++ val_param_substs ++ val_ty_subst
       ++ env_ty_subst ++ ty_subst_lang ++ exp_parameterized ++ val_parameterized
       ++ ty_env_lang.
Definition exists_full : lang := exists_lang ++ poly_full.

(* The OLD checker rejects them (the starting point). *)
Lemma poly_full_old_rejected   : syntactic_sort_eq_langb poly_full   = false.
Proof. vm_compute. reflexivity. Qed.
Lemma exists_full_old_rejected : syntactic_sort_eq_langb exists_full = false.
Proof. vm_compute. reflexivity. Qed.

(* The WEAKENED checker accepts them. *)
Lemma poly_full_accepted   : syntactic_sort_eq_langb' poly_full   = true.
Proof. vm_compute. reflexivity. Qed.
Lemma exists_full_accepted : syntactic_sort_eq_langb' exists_full = true.
Proof. vm_compute. reflexivity. Qed.

(* A gated language (term-eq at index sort [ty] whose witness [w:S] occurs in
   neither equated side — the SubstWfCounterexample3 failure mode) is
   REJECTED. *)
Definition gated_lang : lang :=
  [("bad", term_eq_rule [("w", scon "S" []); ("D", scon "tyenv" [])]
              (con "a" [var "D"]) (con "b" [var "D"]) (scon "ty" [var "D"]));
   ("val", sort_rule [("D", scon "tyenv" []); ("A", scon "ty" [var "D"])] []);
   ("b", term_rule [("D", scon "tyenv" [])] [] (scon "ty" [var "D"]));
   ("a", term_rule [("D", scon "tyenv" [])] [] (scon "ty" [var "D"]));
   ("S", sort_rule [] []);
   ("ty", sort_rule [("D", scon "tyenv" [])] []);
   ("tyenv", sort_rule [] [])].
Lemma gated_rejected : syntactic_sort_eq_langb' gated_lang = false.
Proof. vm_compute. reflexivity. Qed.
