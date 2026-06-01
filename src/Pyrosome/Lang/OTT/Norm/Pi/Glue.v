Set Implicit Arguments.

From coqutil Require Import Datatypes.String.
From Stdlib Require Import Lists.List.
Import ListNotations.
Open Scope string.
Open Scope list.
From Utils Require Import Utils.
From Pyrosome.Theory Require Import Core.
From Pyrosome.Lang.OTT.Norm.Pi Require Import
  Domain Apply Reflect Typing EvalRel Determinism.
Import Core.Notations.

Notation term := (@term string).

(* ===================================================================== *)
(* The GLUING facet of the combined reducibility+gluing model.            *)
(*                                                                        *)
(* Design pivot (2026-06-01): rather than typing semantic values rigidly  *)
(* with [has_svalty] (which cannot validate eta — an eta-expanded         *)
(* [vLam body] lives at the reducibly-but-not-syntactically-equal         *)
(* codomain [B[ARG::wkn]]), the model relates SYNTACTIC OTT terms to       *)
(* semantic values through the typed evaluator [eval_rel] (Pi/EvalRel.v).  *)
(* Value "typing" is then delegated to the syntactic side, where the OTT   *)
(* equational theory ([eq_term], once [ott_pi] is in the language) carries *)
(* the eta law for free.                                                   *)
(*                                                                        *)
(* Two syntactic terms GLUE at a semantic context/type [(Ge, T)] iff they  *)
(* evaluate to a COMMON semantic value (the Pi analogue of                 *)
(* [OTT/Norm/Model.v]'s [glue_exp]).  Because [eval_rel] is deterministic  *)
(* (Pi/Determinism.v), gluing is a partial equivalence relation: the       *)
(* shared value is unique, so symmetry and transitivity are immediate.     *)
(* ===================================================================== *)

(* Gluing of terms at a semantic type, and of types at a context. *)
Definition glue_exp (Ge : senv) (T : svalty) (e1 e2 : term) : Type :=
  { v & (eval_rel Ge e1 T v * eval_rel Ge e2 T v)%type }.

Definition glue_ty (Ge : senv) (A1 A2 : term) : Type :=
  { T & (eval_ty Ge A1 T * eval_ty Ge A2 T)%type }.

(* The shared value / type is determined by either side. *)
Definition glue_exp_val Ge T e1 e2 (g : glue_exp Ge T e1 e2) : sval := projT1 g.

Lemma glue_exp_eval_l : forall Ge T e1 e2 (g : glue_exp Ge T e1 e2),
    eval_rel Ge e1 T (glue_exp_val g).
Proof. intros Ge T e1 e2 [v [h1 h2]]; exact h1. Qed.

Lemma glue_exp_eval_r : forall Ge T e1 e2 (g : glue_exp Ge T e1 e2),
    eval_rel Ge e2 T (glue_exp_val g).
Proof. intros Ge T e1 e2 [v [h1 h2]]; exact h2. Qed.

(* ===================================================================== *)
(* PER structure (from determinism).                                       *)
(* ===================================================================== *)

Lemma glue_exp_sym : forall Ge T e1 e2,
    glue_exp Ge T e1 e2 -> glue_exp Ge T e2 e1.
Proof. intros Ge T e1 e2 [v [h1 h2]]. exists v; split; assumption. Qed.

Lemma glue_exp_trans : forall Ge T e1 e2 e3,
    glue_exp Ge T e1 e2 -> glue_exp Ge T e2 e3 -> glue_exp Ge T e1 e3.
Proof.
  intros Ge T e1 e2 e3 [v [h1 h2]] [w [h2' h3]].
  (* the two derivations on [e2] pin [v = w] *)
  pose proof (eval_rel_det h2 h2') as [_ Hvw]; subst w.
  exists v; split; assumption.
Qed.

(* Gluing of a term with itself is exactly "it evaluates": the diagonal of
   [glue_exp] is the domain of definition of the evaluator. *)
Lemma glue_exp_refl_of_eval : forall Ge T e v,
    eval_rel Ge e T v -> glue_exp Ge T e e.
Proof. intros Ge T e v H. exists v; split; exact H. Qed.

Lemma glue_exp_diag_eval : forall Ge T e,
    glue_exp Ge T e e -> { v & eval_rel Ge e T v }.
Proof. intros Ge T e [v [h _]]. exists v; exact h. Qed.

(* Same structure for type-level gluing. *)
Lemma glue_ty_sym : forall Ge A1 A2, glue_ty Ge A1 A2 -> glue_ty Ge A2 A1.
Proof. intros Ge A1 A2 [T [h1 h2]]. exists T; split; assumption. Qed.

Lemma glue_ty_trans : forall Ge A1 A2 A3,
    glue_ty Ge A1 A2 -> glue_ty Ge A2 A3 -> glue_ty Ge A1 A3.
Proof.
  intros Ge A1 A2 A3 [T [h1 h2]] [U [h2' h3]].
  pose proof (eval_ty_det h2 h2') as [_ HTU]; subst U.
  exists T; split; assumption.
Qed.

(* ===================================================================== *)
(* THE remaining load-bearing theorem (the fundamental lemma, to come):    *)
(*                                                                        *)
(*   eval totality — every well-typed OTT term (in the Pi-extended         *)
(*   language) evaluates: [wf_term fo_pi [] (...) e -> { v & eval_rel ... }]*)
(*                                                                        *)
(* Totality of the relational hereditary substitution [Apply_*] / [Vapp]   *)
(* and of [Reflect] are corollaries (they fire inside [eval_rel]'s subst   *)
(* and variable rules).  This is the normalization content and is proved   *)
(* via the REDUCIBILITY facet of the combined relation (a gluing logical    *)
(* relation indexed by the syntax, whose Pi clause quantifies over          *)
(* [eval_sub]-related substitutions and whose escape lands in [eval_rel] /  *)
(* [eq_term]); the eta-typing obstruction dissolves because the typing      *)
(* lives on the syntactic side.  Built next.                                *)
(* ===================================================================== *)
